{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
module CodeGenerator(codeGen) where

import ParserAST                  (ParserF(..))
import Machine                    (M(..), ΣVar(..), ΣState(..), ΣVars, IMVar(..), MVar(..), ΦVar(..), fmapInstr)
import Indexed                    (IFunctor, Free(Op), History(Era), Void, imap, histo, present, (|>), absurd)
import Utils                      (TExpQ, lift', (>*<), WQ(..))
import Control.Applicative        (liftA2)
import Control.Monad              ((<$!>))
import Control.Monad.Reader       (ReaderT, ask, runReaderT, local)
import Control.Monad.State.Strict (State, get, put, runState, MonadState)
import Data.Map.Strict            (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe                 (isJust, fromJust)
import Debug.Trace                (traceShow)

type IΦVar = Int
newtype CodeGen b xs ks a i = CodeGen {runCodeGen :: forall xs' ks'. Free M Void (a ': xs') ks' b i
                                                  -> ReaderT (Map IMVar IMVar, IMVar, IΦVar) (State ΣVars) (Free M Void xs' ks' b i)}

codeGen :: Free ParserF Void '[] '[] a i -> (Free M Void '[] '[] a i, ΣVars)
codeGen p = let (m, vs) = runState (runReaderT (runCodeGen (histo absurd alg (traceShow p p)) (Op Halt)) (Map.empty, 0, 0)) []
            in traceShow m (m, vs)
  where
    alg = peephole |> (direct . imap present)
    peephole :: ParserF (History ParserF (CodeGen b)) xs ks a i -> Maybe (CodeGen b xs ks a i)
    peephole !(Era _ (Pure f) :<*>: Era p _) = Just $ CodeGen $ \(!m) -> runCodeGen p (fmapInstr f m)
    peephole !(Era _ (Era _ (Pure f) :<*>: Era p _) :<*>: Era q _) = Just $ CodeGen $ \(!m) ->
      do qc <- runCodeGen q (Op (Lift2 f m))
         runCodeGen p qc
    peephole !(Era _ (Try n (Era p _)) :<|>: Era q _) = Just $ CodeGen $ \(!m) ->
      do (_, _, i) <- ask
         let (reg, φ) = case m of
               Op (Join _) -> (Nothing, m)
               m           -> (Just (ΦVar i, m), Op (Join (ΦVar i)))
         pc <- local (trimap id id (+1)) (runCodeGen p (Op (Commit (isJust n) φ)))
         qc <- local (trimap id id (+1)) (runCodeGen q φ)
         return $! Op (SoftFork n pc qc reg)
    peephole !(Era _ (Era _ (Try n (Era p _)) :*>: Era _ (Pure x)) :<|>: Era q _) = Just $ CodeGen $ \(!m) ->
      do (_, _, i) <- ask
         let (reg, φ) = case m of
               Op (Join _) -> (Nothing, m)
               m           -> (Just (ΦVar i, m), Op (Join (ΦVar i)))
         pc <- local (trimap id id (+1)) (runCodeGen p (Op (Commit (isJust n) (Op (Pop (Op (Push x φ)))))))
         qc <- local (trimap id id (+1)) (runCodeGen q φ)
         return $! Op (SoftFork n pc qc reg)
    -- TODO: One more for fmap try
    peephole !(ChainPost (Era _ (Pure x)) (Era op _)) = Just $ CodeGen $ \(!m) ->
      do (_, v, _) <- ask
         σ <- freshΣ (_val x) (_code x)
         opc <- local (trimap id (+1) id) (runCodeGen op (Op (ChainIter σ (MVar v))))
         return $! Op (Push x (Op (ChainInit x σ opc (MVar v) m)))
    peephole _ = Nothing
    direct :: ParserF (CodeGen b) xs ks a i -> CodeGen b xs ks a i
    direct !(Pure x)          = CodeGen $ \(!m) -> do return $! (Op (Push x m))
    direct !(Satisfy p)       = CodeGen $ \(!m) -> do return $! (Op (Sat p m))
    direct !(pf :<*>: px)     = CodeGen $ \(!m) -> do !pxc <- runCodeGen px (Op (Lift2 (lift' ($)) m)); runCodeGen pf pxc
    direct !(p :*>: q)        = CodeGen $ \(!m) -> do !qc <- runCodeGen q m; runCodeGen p (Op (Pop qc))
    direct !(p :<*: q)        = CodeGen $ \(!m) -> do !qc <- runCodeGen q (Op (Pop m)); runCodeGen p qc
    direct !Empty             = CodeGen $ \(!m) -> do return $! Op Empt
    direct !(p :<|>: q)       = CodeGen $ \(!m) ->
      do (_, _, i) <- ask
         let (reg, φ) = case m of
               Op (Join _) -> (Nothing, m)
               m           -> (Just (ΦVar i, m), Op (Join (ΦVar i)))
         pc <- local (trimap id id (+1)) (runCodeGen p (Op (Commit False φ)))
         qc <- local (trimap id id (+1)) (runCodeGen q φ)
         return $! Op (HardFork pc qc reg)
    direct !(Try n p)         = CodeGen $ \(!m) -> do fmap (Op . Attempt n) (runCodeGen p (Op (Commit (isJust n) m)))
    direct !(LookAhead p)     = CodeGen $ \(!m) -> do fmap (Op . Look) (runCodeGen p (Op (Restore m)))
    direct !(NotFollowedBy p) = CodeGen $ \(!m) -> do liftA2 (\p q -> Op (NegLook p q)) (runCodeGen p (Op (Restore (Op Empt)))) (return (Op (Push (lift' ()) m)))
    direct !(Branch b p q)    = CodeGen $ \(!m) -> do !pc <- runCodeGen p (Op (Lift2 (WQ (flip ($)) [||flip ($)||]) m))
                                                      !qc <- runCodeGen q (Op (Lift2 (WQ (flip ($)) [||flip ($)||]) m))
                                                      runCodeGen b (Op (Case pc qc))
    direct !(Match p fs qs)   = CodeGen $ \(!m) -> do !qcs <- traverse (flip runCodeGen m) qs
                                                      runCodeGen p (Op (Choices fs qcs))
    -- NOTE: It is necessary to rename the MVars produced by preprocess
    direct !(Rec !old !q)     = CodeGen $ \(!m) ->
      do (seen, v, _) <- ask
         case Map.lookup old seen of
           Just new -> do return $! Op (MuCall (MVar new) m)
           Nothing  -> do n <- local (trimap (Map.insert old v) (const (v+1)) id) (runCodeGen q (Op Ret))
                          return $! Op (Call n (MVar v) m)
    direct !(ChainPre op p) = CodeGen $ \(!m) ->
      do (_, v, _) <- ask
         σ <- freshΣ id [||id||]
         opc <- local (trimap id (+1) id) (runCodeGen op (fmapInstr (lift' flip >*< lift' (.)) (Op (ChainIter σ (MVar v)))))
         pc <- local (trimap id (+1) id) (runCodeGen p (Op (Lift2 (lift' ($)) m)))
         return $! Op (Push (lift' id) (Op (ChainInit (lift' id) σ opc (MVar v) pc)))
    direct !(ChainPost p op) = CodeGen $ \(!m) ->
      do (_, v, _) <- ask
         σ <- freshΣ Nothing [||Nothing||]
         opc <- local (trimap id (+1) id) (runCodeGen op (fmapInstr (lift' (<$!>)) (Op (ChainIter σ (MVar v)))))
         let m' = Op (ChainInit (WQ Nothing [||Nothing||]) σ opc (MVar v) (fmapInstr (lift' fromJust) m))
         local (trimap id (+1) id) (runCodeGen p (fmapInstr (lift' Just) m'))
    direct !(Debug name p) = CodeGen $ \(!m) -> fmap (Op . LogEnter name) (runCodeGen p (Op (LogExit name m)))

    trimap :: (a -> x) -> (b -> y) -> (c -> z) -> (a, b, c) -> (x, y, z)
    trimap f g h (x, y, z) = (f x, g y, h z)

    freshΣ :: MonadState ΣVars m => a -> TExpQ a -> m (ΣVar a)
    freshΣ x qx = do σs <- get
                     let σ = nextΣ σs
                     put (ΣState x qx σ:σs)
                     return $! σ
      where
        nextΣ []                      = ΣVar 0
        nextΣ (ΣState _ _ (ΣVar x):_) = ΣVar (x+1)