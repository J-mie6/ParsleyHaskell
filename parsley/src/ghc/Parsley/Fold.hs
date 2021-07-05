{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Parsley.Fold
Description : The "folding" combinators: chains and iterators
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module contains the combinator concerned with some form of iteration or input folding. Notably,
this includes the traditional `many` and `some` combinators.

@since 0.1.0.0
-}
module Parsley.Fold (
    many, some, manyN,
    skipMany, skipSome, skipManyN,
    sepBy, sepBy1, endBy, endBy1, sepEndBy, sepEndBy1,
    chainl1, chainr1, chainl, chainr,
    infixl1, infixr1, prefix, postfix,
    manyr, manyl,
    somer, somel
  ) where

import Prelude hiding      (pure, (<*>), (<$>), (*>), (<*))
import Parsley.Alternative ((<|>), option)
import Parsley.Applicative (pure, (<*>), (<$>), (*>), (<*), (<:>), (<**>), void)
import Parsley.Internal    (Parser, Defunc(FLIP, ID, COMPOSE, EMPTY, CONS, CONST), ParserOps, pattern FLIP_H, pattern COMPOSE_H, pattern UNIT, prefix, postfix)
import Parsley.Register    (bind, get, modify, newRegister_)

{-prefix :: Parser (a -> a) -> Parser a -> Parser a
prefix op p = newRegister_ ID $ \acc ->
  let go = modify acc (FLIP_H COMPOSE <$> op) *> go
       <|> get acc
  in go <*> p-}

{-postfix :: Parser a -> Parser (a -> a) -> Parser a
postfix p op = newRegister p $ \acc ->
  let go = modify acc op *> go
       <|> get acc
  in go-}

-- Parser Folds
{-|
@manyr f k p@ parses __zero__ or more @p@s and combines the results using the function @f@. When @p@
fails without consuming input, the terminal result @k@ is returned.

> many = manyr CONS EMPTY

@since 0.1.0.0
-}
manyr :: (ParserOps repf, ParserOps repk) => repf (a -> b -> b) -> repk b -> Parser a -> Parser b
manyr f k p = prefix (f <$> p) (pure k)

{-|
@somer f k p@ parses __one__ or more @p@s and combines the results using the function @f@. When @p@
fails without consuming input, the terminal result @k@ is returned.

> some = somer CONS EMPTY

@since 0.1.0.0
-}
somer :: (ParserOps repf, ParserOps repk) => repf (a -> b -> b) -> repk b -> Parser a -> Parser b
somer f k p = f <$> p <*> manyr f k p

{-|
@manyl f k p@ parses __zero__ or more @p@s and combines the results using the function @f@. The
accumulator is initialised with the value @k@.

@since 0.1.0.0
-}
manyl :: (ParserOps repf, ParserOps repk) => repf (b -> a -> b) -> repk b -> Parser a -> Parser b
manyl f k p = postfix (pure k) ((FLIP <$> pure f) <*> p)

{-|
@somel f k p@ parses __one__ or more @p@s and combines the results using the function @f@. The
accumulator is initialised with the value @k@.

@since 0.1.0.0
-}
somel :: (ParserOps repf, ParserOps repk) => repf (b -> a -> b) -> repk b -> Parser a -> Parser b
somel f k p = postfix (f <$> pure k <*> p) ((FLIP <$> pure f) <*> p)

-- Chain Combinators
{-|
@infixl1 wrap p op @ parses one or more occurrences of @p@, separated by @op@. Returns a value obtained
by a /left/ associative application of all functions returned by @op@ to the values returned by @p@.
The function @wrap@ is used to transform the initial value from @p@ into the correct form.

@since 2.0.0.0
-}
infixl1 :: ParserOps rep => rep (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
infixl1 f p op = postfix (f <$> p) (FLIP <$> op <*> p)

{-|
The classic version of the left-associative chain combinator. See `infixl1`.

> chainl1 p op = infixl1 ID p op

@since 0.1.0.0
-}
chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 = infixl1 ID

{-|
@infixr1 wrap p op @ parses one or more occurrences of @p@, separated by @op@. Returns a value obtained
by a /right/ associative application of all functions returned by @op@ to the values returned by @p@.
The function @wrap@ is used to transform the final value from @p@ into the correct form.

@since 2.0.0.0
-}
infixr1 :: ParserOps rep => rep (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
infixr1 f p op = newRegister_ ID $ \acc ->
  let go = bind p $ \x ->
           modify acc (FLIP_H COMPOSE <$> (op <*> x)) *> go
       <|> f <$> x
  in go <**> get acc

{-|
The classic version of the right-associative chain combinator. See `infixr1`.

> chainr1 p op = infixr1 ID p op

@since 0.1.0.0
-}
chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 = infixr1 ID

{-|
Like `chainr1`, but may parse zero occurences of @p@ in which case the value is returned.

@since 0.1.0.0
-}
chainr :: ParserOps rep => Parser a -> Parser (a -> a -> a) -> rep a -> Parser a
chainr p op x = option x (chainr1 p op)

{-|
Like `chainl1`, but may parse zero occurences of @p@ in which case the value is returned.

@since 0.1.0.0
-}
chainl :: ParserOps rep => Parser a -> Parser (a -> a -> a) -> rep a -> Parser a
chainl p op x = option x (chainl1 p op)

-- Derived Combinators
{-|
Attempts to parse the given parser __zero__ or more times, collecting all of the successful results
into a list. Same as @manyN 0@

@since 0.1.0.0
-}
many :: Parser a -> Parser [a]
many = manyr CONS EMPTY

{-|
Attempts to parse the given parser __n__ or more times, collecting all of the successful results
into a list.

@since 0.1.0.0
-}
manyN :: Int -> Parser a -> Parser [a]
manyN n p = foldr (const (p <:>)) (many p) [1..n]

{-|
Attempts to parse the given parser __one__ or more times, collecting all of the successful results
into a list. Same as @manyN 1@

@since 0.1.0.0
-}
some :: Parser a -> Parser [a]
some = manyN 1

{-|
Like `many`, excepts discards its results.

@since 0.1.0.0
-}
skipMany :: Parser a -> Parser ()
--skipMany p = let skipManyp = p *> skipManyp <|> unit in skipManyp
skipMany = void . manyl CONST UNIT -- the void here will encourage the optimiser to recognise that the register is unused

{-|
Like `manyN`, excepts discards its results.

@since 0.1.0.0
-}
skipManyN :: Int -> Parser a -> Parser ()
skipManyN n p = foldr (const (p *>)) (skipMany p) [1..n]

{-|
Like `some`, excepts discards its results.

@since 0.1.0.0
-}
skipSome :: Parser a -> Parser ()
skipSome = skipManyN 1

{-|
@sepBy p sep@ parses __zero__ or more occurrences of @p@, separated by @sep@.
Returns a list of values returned by @p@.

@since 0.1.0.0
-}
sepBy :: Parser a -> Parser b -> Parser [a]
sepBy p sep = option EMPTY (sepBy1 p sep)

{-|
@sepBy1 p sep@ parses __one__ or more occurrences of @p@, separated by @sep@.
Returns a list of values returned by @p@.

@since 0.1.0.0
-}
sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p sep = p <:> many (sep *> p)

{-|
@endBy p sep@ parses __zero__ or more occurrences of @p@, separated and ended by @sep@.
Returns a list of values returned by @p@.

@since 0.1.0.0
-}
endBy :: Parser a -> Parser b -> Parser [a]
endBy p sep = many (p <* sep)

{-|
@endBy1 p sep@ parses __one__ or more occurrences of @p@, separated and ended by @sep@.
Returns a list of values returned by @p@.

@since 0.1.0.0
-}
endBy1 :: Parser a -> Parser b -> Parser [a]
endBy1 p sep = some (p <* sep)

{-|
@sepEndBy p sep@ parses __zero__ or more occurrences of @p@, separated and /optionally/ ended by @sep@.
Returns a list of values returned by @p@.

@since 0.1.0.0
-}
sepEndBy :: Parser a -> Parser b -> Parser [a]
sepEndBy p sep = option EMPTY (sepEndBy1 p sep)

{-|
@sepEndBy1 p sep@ parses __one__ or more occurrences of @p@, separated and /optionally/ ended by @sep@.
Returns a list of values returned by @p@.

@since 0.1.0.0
-}
sepEndBy1 :: Parser a -> Parser b -> Parser [a]
sepEndBy1 p sep = newRegister_ ID $ \acc ->
  let go = modify acc (COMPOSE_H (FLIP_H COMPOSE) CONS <$> p)
         *> (sep *> (go <|> get acc) <|> get acc)
  in go <*> pure EMPTY

{-sepEndBy1 :: Parser a -> Parser b -> Parser [a]
sepEndBy1 p sep =
  let seb1 = p <**> (sep *> (FLIP_H CONS <$> option EMPTY seb1)
                 <|> pure (APP_H (FLIP_H CONS) EMPTY))
  in seb1-}