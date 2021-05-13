{-# LANGUAGE MultiParamTypeClasses #-}
module Parsley.Precedence (module Parsley.Precedence) where

import Prelude hiding                ((<$>), (<*>), pure)
import Data.List                     (foldl')

import Parsley.Alternative           (choice, (<|>))
import Parsley.Applicative           ((<$>), (<*>), pure, (<**>))
import Parsley.Fold                  (prefix, postfix, infixl1, infixr1)
import Parsley.Internal.Common.Utils (WQ(WQ))
import Parsley.Internal.Core         (Parser, Defunc(BLACK, ID, FLIP))

precedence :: Prec a -> Parser a
precedence (Atom atom) = atom
precedence (Level lvls op) = level (precedence lvls) op
  where
    level :: Parser a -> Op a b -> Parser b
    level atom (Op InfixL op wrap) = infixl1 wrap atom op
    level atom (Op InfixR op wrap) = infixr1 wrap atom op
    level atom (Op InfixN op wrap) = atom <**> (FLIP <$> op <*> atom <|> pure wrap)
    level atom (Op Prefix op wrap) = prefix op (wrap <$> atom)
    level atom (Op Postfix op wrap) = postfix (wrap <$> atom) op

precHomo :: Parser a -> [Op a a] -> Parser a
precHomo atom = precedence . foldl' (>+) (Atom atom)

data Fixity a b sig where
  InfixL  :: Fixity a b (b -> a -> b)
  InfixR  :: Fixity a b (a -> b -> b)
  InfixN  :: Fixity a b (a -> a -> b)
  Prefix  :: Fixity a b (b -> b)
  Postfix :: Fixity a b (b -> b)

data Op a b where
  Op :: Fixity a b sig -> Parser sig -> Defunc (a -> b) -> Op a b

gops :: Fixity a b sig -> [Parser sig] -> WQ (a -> b) -> Op a b
gops fixity ps wrap = Op fixity (choice ps) (BLACK wrap)

ops :: Fixity a a sig -> [Parser sig] -> Op a a
ops fixity ps = Op fixity (choice ps) ID

class Subtype sub sup where
  upcast   :: sub -> sup
  downcast :: sup -> Maybe sub

sops :: Subtype a b => Fixity a b sig -> [Parser sig] -> Op a b
sops fixity ps = gops fixity ps (WQ upcast [||upcast||])

data Prec a where
  Level :: Prec a -> Op a b -> Prec b
  Atom :: Parser a -> Prec a

infixl 5 >+
(>+) :: Prec a -> Op a b -> Prec b
(>+) = Level

infixr 5 +<
(+<) :: Op a b -> Prec a -> Prec b
(+<) = flip (>+)