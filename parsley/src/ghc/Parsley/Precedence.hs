{-# LANGUAGE MultiParamTypeClasses #-}
{-|
Module      : Parsley.Precedence
Description : The precedence parser functionality
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module exposes the required machinery for parsing expressions given by a precedence
table. Unlike those found in [parser-combinators](https://hackage.haskell.org/package/parser-combinators-1.3.0/docs/Control-Monad-Combinators-Expr.html)
or [parsec](https://hackage.haskell.org/package/parsec-3.1.14.0/docs/Text-Parsec-Expr.html), this
implementation allows the precedence layers to change type in the table.

@since 0.1.0.0
-}
module Parsley.Precedence (module Parsley.Precedence) where

import Prelude hiding      ((<$>), (<*>), pure)
import Data.List           (foldl')

import Parsley.Alternative (choice, (<|>))
import Parsley.Applicative ((<$>), (<*>), pure, (<**>))
import Parsley.Fold        (prefix, postfix, infixl1, infixr1)
import Parsley.Internal    (WQ, Parser, Defunc(BLACK, ID, FLIP), makeQ)

{-|
This combinator will construct and expression parser will provided with a table of precedence along
with a terminal atom.

@since 2.0.0.0
-}
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

{-|
A simplified version of `precedence` that does not use the heterogeneous list `Prec`, but
instead requires all layers of the table to have the same type.

@since 2.0.0.0
-}
precHomo :: Parser a -> [Op a a] -> Parser a
precHomo atom = precedence . foldl' (>+) (Atom atom)

{-|
A heterogeneous list that represents a precedence table so that @Prec a@ synthesises values of
type @a@ via various layers of operators.

@since 2.0.0.0
-}
data Prec a where
  Level :: Prec a -> Op a b -> Prec b
  Atom :: Parser a -> Prec a

{-|
This datatype represents levels of the precedence table `Prec`, where each constructor
takes many parsers of the same level and fixity.

@since 2.0.0.0
-}
data Op a b where
  Op :: Fixity a b sig -> Parser sig -> Defunc (a -> b) -> Op a b

data Fixity a b sig where
  InfixL  :: Fixity a b (b -> a -> b)
  InfixR  :: Fixity a b (a -> b -> b)
  InfixN  :: Fixity a b (a -> a -> b)
  Prefix  :: Fixity a b (b -> b)
  Postfix :: Fixity a b (b -> b)

{-
data Level a b = InfixL  [Parser (b -> a -> b)] (Defunc (a -> b)) -- ^ left-associative infix operators
               | InfixR  [Parser (a -> b -> b)] (Defunc (a -> b)) -- ^ right-associative infix operators
               | Prefix  [Parser (b -> b)]      (Defunc (a -> b)) -- ^ prefix unary operators
               | Postfix [Parser (b -> b)]      (Defunc (a -> b)) -- ^ postfix unary operators
-}

gops :: Fixity a b sig -> [Parser sig] -> WQ (a -> b) -> Op a b
gops fixity ps wrap = Op fixity (choice ps) (BLACK wrap)

ops :: Fixity a a sig -> [Parser sig] -> Op a a
ops fixity ps = Op fixity (choice ps) ID

class Subtype sub sup where
  upcast   :: sub -> sup
  downcast :: sup -> Maybe sub

sops :: Subtype a b => Fixity a b sig -> [Parser sig] -> Op a b
sops fixity ps = gops fixity ps (makeQ upcast [||upcast||])

infixl 5 >+
(>+) :: Prec a -> Op a b -> Prec b
(>+) = Level

infixr 5 +<
(+<) :: Op a b -> Prec a -> Prec b
(+<) = flip (>+)