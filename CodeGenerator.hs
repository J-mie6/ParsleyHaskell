{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternSynonyms #-}
--{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
module CodeGenerator (codeGen, halt, ret) where

import ParserAST                  (ParserF(..))
import MachineAST                 (M(..), MetaM(..), IMVar, IΦVar, IΣVar, MVar(..), ΦVar(..), ΣVar(..), _Fmap, _App, _Modify, addCoins, refundCoins, drainCoins, freeCoins)
import MachineAnalyser            (coinsNeeded)
import CombinatorAnalyser         (compliance, Compliance(..))
import Indexed                    (IFunctor, Fix, Fix3(In3), Cofree(..), imap, histo, extract, (|>), (/\), ifst, isnd, (:*:)(..))
import Utils                      (code, (>*<), WQ(..))
import Defunc                     (Defunc(BLACK))
import Control.Applicative        (liftA2)
import Control.Monad.Reader       (Reader, ask, asks, runReader, local, MonadReader)
import Control.Monad.State.Strict (State, get, modify', runState, MonadState)
import Fresh                      (VFreshT, HFresh, runFreshT, runFresh, evalFreshT, construct, MonadFresh(..), mapVFreshT)
import Control.Monad.Trans        (lift)
import Data.Set                   (Set)
import Data.Maybe                 (isJust)
import Debug.Trace                (traceShow, trace)
import Data.Void                  (Void)
import qualified Data.Set as Set

type CodeGenStack a = VFreshT IΦVar (VFreshT IMVar (HFresh IΣVar)) a
runCodeGenStack :: CodeGenStack a -> IMVar -> IΦVar -> IΣVar -> (a, IΣVar)
runCodeGenStack m μ0 φ0 σ0 = 
  (flip runFresh σ0 . 
   flip evalFreshT μ0 . 
   flip evalFreshT φ0) m

newtype CodeGen o b a = 
  CodeGen {runCodeGen :: forall xs r. Bool -> Fix3 (M o) (a ': xs) r b -> CodeGenStack (Fix3 (M o) xs r b, Bool)}

halt :: Fix3 (M o) '[a] Void a
halt = In3 Halt

ret :: Fix3 (M o) '[x] x a
ret = In3 Ret

codeGen :: {-forall o xs r a b. -}Fix ParserF a -> Fix3 (M o) (a ': xs) r b -> IMVar -> IΣVar -> (Fix3 (M o) xs r b, IΣVar)
codeGen p terminal μ0 σ0 = trace ("GENERATING: " ++ show p ++ "\nMACHINE: " ++ show m) $ (m, maxΣ)
  where
    (m, maxΣ) = finalise (ifst (histo alg p))
    --alg :: forall a. ParserF (Cofree ParserF (CodeGen o b :*: Compliance)) a -> (CodeGen o b :*: Compliance) a
    alg = {-peephole |> -}(\x -> CodeGen (direct (imap extract x))) /\ (compliance . imap (isnd . extract))
    
    --finalise :: CodeGen o b a -> (Fix3 (M o) xs r b, IΣVar)
    finalise cg = 
      let ((m, _), maxΣ) = runCodeGenStack (runCodeGen cg False terminal) μ0 0 σ0 
          n = coinsNeeded m
      in (addCoins n m, maxΣ)

--pattern f :<$>: p <- (_ :< Pure f) :<*>: (p :< _)
--pattern p :$>: x <- (_ :< p) :*>: (_ :< Pure x)
--pattern LiftA2 f p q <- (_ :< ((_ :< Pure f) :<*>: (p :< _))) :<*>: (q :< _)
--pattern TryOrElse p q <- (_ :< Try (p :< _)) :<|>: (q :< _)

{-peephole :: ParserF (Cofree ParserF (CodeGen o b)) a -> Maybe (CodeGen o b a)
peephole (f :<$>: p) = Just $ CodeGen $ \m -> runCodeGen p (In3 (_Fmap f m))
peephole (LiftA2 f p q) = Just $ CodeGen $ \m ->
  do qc <- runCodeGen q (In3 (Lift2 (BLACK f) m))
     runCodeGen p qc
peephole (TryOrElse p q) = Just $ CodeGen $ \m ->
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation φ))
     fmap (binder . In3 . SoftFork pc) (freshΦ (runCodeGen q φ))
peephole ((_ :< ((Try (p :< _)) :$>: x)) :<|>: (q :< _)) = Just $ CodeGen $ \m ->
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation (In3 (Pop (In3 (Push x φ))))))
     fmap (binder . In3 . SoftFork pc) (freshΦ (runCodeGen q φ))
-- TODO: One more for fmap try
peephole _ = Nothing-}

(><) :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
(f >< g) (x, y) = (f x, g y)

biliftA2 :: (a -> b -> c) -> (x -> y -> z) -> (a, x) -> (b, y) -> (c, z)
biliftA2 f g (x1, y1) (x2, y2) = (f x1 x2, g y1 y2)

direct :: ParserF (CodeGen o b :*: Compliance) a -> Bool -> Fix3 (M o) (a ': xs) r b -> CodeGenStack (Fix3 (M o) xs r b, Bool)
direct (Pure x)    cut   m = do return $! (In3 (Push x m), False)
direct (Satisfy p) True  m = do return $! (In3 (Sat p (addCoins (coinsNeeded m) m)), True)
direct (Satisfy p) False m = do return $! (In3 (Sat p m), True)
direct (pf :<*>: px) cut m = mdo (pfc, handled) <- runCodeGen (ifst pf) cut pxc
                                 (pxc, handled') <- runCodeGen (ifst px) (cut && not handled) (In3 (_App m))
                                 return $! (pfc, handled')
direct (p :*>: q) cut m = mdo (pc, handled) <- runCodeGen (ifst p) cut (In3 (Pop qc))
                              (qc, handled') <- runCodeGen (ifst q) (cut && not handled) m
                              return $! (pc, handled')
direct (p :<*: q) cut m = mdo (pc, handled) <- runCodeGen (ifst p) cut qc
                              (qc, handled') <- runCodeGen (ifst q) (cut && not handled) (In3 (Pop m))
                              return $! (pc, handled')
direct Empty cut m   = do return $! (In3 Empt, False)
direct ((p :*: NonComp) :<|>: (q :*: FullPure)) _ m = 
  do (binder, φ) <- makeΦ m
     (pc, _) <- freshΦ (runCodeGen p True (deadCommitOptimisation φ))
     (qc, _) <- freshΦ (runCodeGen q False φ)
     return $! (binder (In3 (HardFork pc qc)), True)
direct (p :<|>: q)       cut m = 
  do (binder, φ) <- makeΦ m
     (pc, _) <- freshΦ (runCodeGen (ifst p) False (deadCommitOptimisation φ))
     (qc, handled) <- freshΦ (runCodeGen (ifst q) cut φ)
     let np = coinsNeeded pc
     let nq = coinsNeeded qc
     let dp = np - (min np nq)
     let dq = nq - (min np nq)
     return $! (binder (In3 (HardFork (addCoins dp pc) (addCoins dq qc))), handled)
direct (Try p)           cut m = do fmap ((In3 . Attempt) >< const False) (runCodeGen (ifst p) False (deadCommitOptimisation m))
direct (LookAhead p)     cut m = 
  do n <- fmap (coinsNeeded . fst) (runCodeGen (ifst p) cut (In3 Empt)) -- Dodgy hack, but oh well
     (pc, handled) <- runCodeGen (ifst p) cut (In3 (Swap (In3 (Seek (refundCoins n m)))))
     return $! (In3 (Tell pc), handled)
direct (NotFollowedBy p) _ m = 
  do (pc, _) <- runCodeGen (ifst p) False (In3 (Pop (In3 (Seek (In3 (Commit (In3 Empt)))))))
     let np = coinsNeeded pc
     let nm = coinsNeeded m
     return $! (In3 (SoftFork (addCoins (max (np - nm) 0) (In3 (Tell pc))) (In3 (Push (code ()) m))), False)
direct (Branch b p q)    cut m = 
  mdo (binder, φ) <- makeΦ m
      let minc = coinsNeeded (In3 (Case pc qc))
      let dp = max 0 (coinsNeeded pc - minc)
      let dq = max 0 (coinsNeeded qc - minc)
      (bc, handled) <- runCodeGen (ifst b) cut (In3 (Case (addCoins dp pc) (addCoins dq qc))) 
      (pc, handled') <- freshΦ (runCodeGen (ifst p) (cut && not handled) (In3 (Swap (In3 (_App φ)))))
      (qc, handled'') <- freshΦ (runCodeGen (ifst q) (cut && not handled) (In3 (Swap (In3 (_App φ)))))
      return $! (binder bc, handled' && handled'')
direct (Match p fs qs def) cut m = 
  mdo (binder, φ) <- makeΦ m
      (pc, handled) <- runCodeGen (ifst p) cut (In3 (Choices fs qcs' defc'))
      let process q = liftA2 (biliftA2 (:) (&&)) (freshΦ (runCodeGen (ifst q) (cut && not handled) φ))
      (qcs, handled'') <- foldr process (return ([], handled')) qs
      (defc, handled') <- freshΦ (runCodeGen (ifst def) (cut && not handled) φ)
      let minc = coinsNeeded (In3 (Choices fs qcs defc))
      let defc':qcs' = map (max 0 . subtract minc . coinsNeeded >>= addCoins) (defc:qcs)
      return $! (binder pc, handled'')
direct (Let _ μ _) True m = return $! (tailCallOptimise μ m, False)
direct (Let _ μ _) False m = return $! (tailCallOptimise μ (addCoins (coinsNeeded m) m), False)
direct (ChainPre (op :*: NonComp) p) _ m =
  do μ <- askM
     σ <- freshΣ
     (opc, _) <- trace "sup" freshM (runCodeGen op True (In3 (_Fmap ([flip (code (.))]) (In3 (_Modify σ (In3 (ChainIter σ μ)))))))
     (pc, _) <- trace "sup" freshM (runCodeGen (ifst p) False (In3 (_App m)))
     return $! (In3 (Push (code id) (In3 (Make σ (In3 (ChainInit σ opc μ (In3 (Get σ (addCoins (coinsNeeded pc) pc)))))))), True)
direct (ChainPre op p) cut m =
  do μ <- askM
     σ <- freshΣ
     (opc, _) <- freshM (runCodeGen (ifst op) False (In3 (_Fmap ([flip (code (.))]) (In3 (_Modify σ (In3 (ChainIter σ μ)))))))
     let nop = coinsNeeded opc
     (pc, handled) <- freshM (runCodeGen (ifst p) cut (In3 (_App m)))
     let addCoinsP = if cut then id else addCoins (coinsNeeded pc)
     return $! (In3 (Push (code id) (In3 (Make σ (In3 (ChainInit σ (addCoins nop opc) μ (In3 (Get σ (addCoinsP pc)))))))), handled)
direct (ChainPost p (op :*: NonComp)) cut m =
  do μ <- askM
     σ <- freshΣ
     let nm = coinsNeeded m
     (opc, _) <- freshM (runCodeGen op True (In3 (_Modify σ (In3 (ChainIter σ μ)))))
     (pc, _) <- freshM (runCodeGen (ifst p) cut (In3 (Make σ (In3 (ChainInit σ opc μ (In3 (Get σ (addCoins nm m))))))))
     return $! (pc, True)
direct (ChainPost p op) cut m =
  mdo μ <- askM
      σ <- freshΣ
      let nm = coinsNeeded m
      (opc, _) <- freshM (runCodeGen (ifst op) False (In3 (_Modify σ (In3 (ChainIter σ μ)))))
      let nop = coinsNeeded opc
      let addCoinsM = if cut && handled then addCoins nm else id
      (pc, handled) <- freshM (runCodeGen (ifst p) cut (In3 (Make σ (In3 (ChainInit σ (addCoins nop opc) μ (In3 (Get σ (addCoinsM m))))))))
      return $! (pc, handled)
direct (Debug name p) cut m = do fmap ((In3 . LogEnter name) >< id) (runCodeGen (ifst p) cut (In3 (LogExit name m)))

tailCallOptimise :: MVar x -> Fix3 (M o) (x ': xs) r a -> Fix3 (M o) xs r a
tailCallOptimise μ (In3 Ret) = In3 (Jump μ)
tailCallOptimise μ k         = In3 (Call μ k)

-- Thanks to the optimisation applied to the K stack, commit is deadcode before Ret or Halt
-- However, I'm not yet sure about the interactions with try yet...
deadCommitOptimisation :: Fix3 (M o) xs r a -> Fix3 (M o) xs r a
deadCommitOptimisation (In3 Ret)  = In3 Ret
deadCommitOptimisation (In3 Halt) = In3 Halt
deadCommitOptimisation m          = In3 (Commit m)

-- Refactor with asks
askM :: CodeGenStack (MVar a)
askM = lift (construct MVar)

askΦ :: CodeGenStack (ΦVar a)
askΦ = construct ΦVar

freshM :: CodeGenStack a -> CodeGenStack a
freshM = mapVFreshT newScope

freshΦ :: CodeGenStack a -> CodeGenStack a
freshΦ = newScope

makeΦ :: Fix3 (M o) (x ': xs) r a -> CodeGenStack (Fix3 (M o) xs r a -> Fix3 (M o) xs r a, Fix3 (M o) (x ': xs) r a)
makeΦ m | elidable m = return $! (id, m)
  where
    -- This is double-φ optimisation:   If a φ-node points directly to another φ-node, then it can be elided
    elidable (In3 (Join _)) = True
    -- This is terminal-φ optimisation: If a φ-node points directly to a terminal operation, then it can be elided
    elidable (In3 Ret)      = True
    elidable (In3 Halt)     = True
    elidable _              = False
makeΦ m = let n = coinsNeeded m in fmap (\φ -> (In3 . MkJoin φ (addCoins n m), drainCoins n (In3 (Join φ)))) askΦ

freshΣ :: CodeGenStack (ΣVar a)
freshΣ = lift (lift (construct ΣVar))
