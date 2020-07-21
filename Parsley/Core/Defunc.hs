{-# LANGUAGE PatternSynonyms #-}
module Parsley.Core.Defunc (module Parsley.Core.Defunc) where

import Parsley.Common.Utils (WQ(..), Code, Quapplicative(..))

data Defunc rep a where
  APP     :: Defunc rep ((a -> b) -> a -> b)
  COMPOSE :: Defunc rep ((b -> c) -> (a -> b) -> (a -> c))
  FLIP    :: Defunc rep ((a -> b -> c) -> b -> a -> c)
  APP_H   :: Defunc rep (a -> b) -> Defunc rep a -> Defunc rep b
  EQ_H    :: Eq a => Defunc rep a -> Defunc rep (a -> Bool)
  CHAR    :: Char -> Defunc rep Char
  ID      :: Defunc rep (a -> a)
  CONS    :: Defunc rep (a -> [a] -> [a])
  CONST   :: Defunc rep (a -> b -> a)
  EMPTY   :: Defunc rep [a]
  UNIT    :: Defunc rep ()
  BLACK   :: rep a -> Defunc rep a

instance Quapplicative (Defunc WQ) where
  makeQ x qx       = BLACK (makeQ x qx)
  _val APP         = ($)
  _val COMPOSE     = (.)
  _val FLIP        = flip
  _val (APP_H f x) = (_val f) (_val x)
  _val (CHAR c)    = c
  _val (EQ_H x)    = ((_val x) ==)
  _val ID          = id
  _val CONS        = (:)
  _val CONST       = const
  _val EMPTY       = []
  _val UNIT        = ()
  _val (BLACK f)   = _val f
  _code = genDefunc

pattern COMPOSE_H :: () => ((x -> y -> z) ~ ((b -> c) -> (a -> b) -> a -> c)) => Defunc rep x -> Defunc rep y -> Defunc rep z
pattern COMPOSE_H f g = APP_H (APP_H COMPOSE f) g
pattern FLIP_H :: () => ((x -> y) ~ ((a -> b -> c) -> b -> a -> c)) => Defunc rep x -> Defunc rep y
pattern FLIP_H f      = APP_H FLIP f
pattern FLIP_CONST :: () => (x ~ (a -> b -> b)) => Defunc rep x
pattern FLIP_CONST    = FLIP_H CONST

genDefunc :: Defunc WQ a -> Code a
genDefunc APP             = [|| \f x -> f x ||]
genDefunc COMPOSE         = [|| \f g x -> f (g x) ||]
genDefunc FLIP            = [|| \f x y -> f y x ||]
genDefunc (COMPOSE_H f g) = [|| \x -> $$(genDefunc1 (COMPOSE_H f g) [||x||]) ||]
genDefunc CONST           = [|| \x _ -> x ||]
genDefunc FLIP_CONST      = [|| \_ y -> y ||]
genDefunc (FLIP_H f)      = [|| \x -> $$(genDefunc1 (FLIP_H f) [||x||]) ||]
genDefunc (APP_H f x)     = genDefunc2 APP (genDefunc f) (genDefunc x)
genDefunc (CHAR c)        = [|| c ||]
genDefunc (EQ_H x)        = [|| \y -> $$(genDefunc x) == y ||]
genDefunc ID              = [|| \x -> x ||]
genDefunc CONS            = [|| \x xs -> x : xs ||]
genDefunc EMPTY           = [|| [] ||]
genDefunc UNIT            = [|| () ||]
genDefunc (BLACK f)       = _code f

genDefunc1 :: Defunc WQ (a -> b) -> Code a -> Code b
genDefunc1 APP             qf = [|| \x -> $$qf x ||]
genDefunc1 COMPOSE         qf = [|| \g x -> $$qf (g x) ||]
genDefunc1 FLIP            qf = [|| \x y -> $$qf y x ||]
genDefunc1 (COMPOSE_H f g) qx = [|| $$(genDefunc1 f (genDefunc1 g qx)) ||]
genDefunc1 CONST           qx = [|| \_ -> $$qx ||]
genDefunc1 FLIP_CONST      _  = genDefunc ID
genDefunc1 (FLIP_H f)      qx = [|| \y -> $$(genDefunc2 (FLIP_H f) qx [||y||]) ||]
genDefunc1 (EQ_H x)        qy = [|| $$(genDefunc x)  == $$qy ||]
genDefunc1 ID              qx = qx
genDefunc1 f               qx = [|| $$(genDefunc f) $$qx ||]

genDefunc2 :: Defunc WQ (a -> b -> c) -> Code a -> Code b -> Code c
genDefunc2 APP        qf qx  = [|| $$qf $$qx ||]
genDefunc2 COMPOSE    qf qg  = [|| \x -> $$qf ($$qg x) ||]
genDefunc2 FLIP       qf qx  = [|| \y -> $$qf y $$qx ||]
genDefunc2 CONST      qx _   = qx
genDefunc2 FLIP_CONST _  qy  = qy
genDefunc2 (FLIP_H f) qx qy  = genDefunc2 f qy qx
genDefunc2 CONS       qx qxs = [|| $$qx : $$qxs ||]
genDefunc2 f          qx qy  = [|| $$(genDefunc f) $$qx $$qy ||]

instance Show (Defunc rep a) where
  show APP = "($)"
  show COMPOSE = "(.)"
  show FLIP = "flip"
  show (FLIP_H f) = concat ["(flip ", show f, ")"]
  show (COMPOSE_H f g) = concat ["(", show f, " . ", show g, ")"]
  show (APP_H f x) = concat ["(", show f, " ", show x, ")"]
  show (CHAR c) = show c
  show (EQ_H x) = concat ["(== ", show x, ")"]
  show ID  = "id"
  show EMPTY = "[]"
  show CONS = "(:)"
  show CONST = "const"
  show UNIT = "()"
  show _ = "x"