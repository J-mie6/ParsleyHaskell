module Parsley.Core.Primitives (ParserR, Id(..), module Parsley.Core.Primitives) where

import Parsley.Core.CombinatorAST (Combinator(..), ScopeRegister(..), Reg(..), ParserR(..))
import Parsley.Core.Defunc        (Defunc)
import Parsley.Common.Indexed     (Fix(In), (:+:)(..))
import Parsley.Common.Utils       (WQ, Id(..))

type Parser a = ParserR WQ a

-- Core smart constructors
{-# INLINE _pure #-}
_pure :: Defunc r a -> ParserR r a
_pure = Parser . In . L . Pure

infixl 4 <*>
(<*>) :: ParserR r (a -> b) -> ParserR r a -> ParserR r b
Parser p <*> Parser q = Parser (In (L (p :<*>: q)))

infixl 4 <*
(<*) :: ParserR r a -> ParserR r b -> ParserR r a
Parser p <* Parser q = Parser (In (L (p :<*: q)))

infixl 4 *>
(*>) :: ParserR r a -> ParserR r b -> ParserR r b
Parser p *> Parser q = Parser (In (L (p :*>: q)))

empty :: ParserR r a
empty = Parser (In (L Empty))

infixr 3 <|>
(<|>) :: ParserR r a -> ParserR r a -> ParserR r a
Parser p <|> Parser q = Parser (In (L (p :<|>: q)))

{-# INLINE _satisfy #-}
_satisfy :: Defunc r (Char -> Bool) -> ParserR r Char
_satisfy = Parser . In . L . Satisfy

lookAhead :: ParserR r a -> ParserR r a
lookAhead = Parser . In . L . LookAhead . unParser

notFollowedBy :: ParserR r a -> ParserR r ()
notFollowedBy = Parser . In . L . NotFollowedBy . unParser

try :: ParserR r a -> ParserR r a
try = Parser . In . L . Try . unParser

{-# INLINE _conditional #-}
_conditional :: [(Defunc r (a -> Bool), ParserR r b)] -> ParserR r a -> ParserR r b -> ParserR r b
_conditional cs (Parser p) (Parser def) =
  let (fs, qs) = unzip cs
  in Parser (In (L (Match p fs (map unParser qs) def)))

branch :: ParserR r (Either a b) -> ParserR r (a -> c) -> ParserR r (b -> c) -> ParserR r c
branch (Parser c) (Parser p) (Parser q) = Parser (In (L (Branch c p q)))

chainPre :: ParserR r (a -> a) -> ParserR r a -> ParserR r a
chainPre (Parser op) (Parser p) = Parser (In (L (ChainPre op p)))

chainPost :: ParserR r a -> ParserR r (a -> a) -> ParserR r a
chainPost (Parser p) (Parser op) = Parser (In (L (ChainPost p op)))

newRegister :: ParserR r a -> (forall r1. Reg r1 a -> ParserR r b) -> ParserR r b
newRegister (Parser p) f = Parser (In (R (ScopeRegister p (unParser . f))))

get :: Reg r1 a -> ParserR r a
get (Reg reg) = Parser (In (L (GetRegister reg)))

put :: Reg r1 a -> ParserR r a -> ParserR r ()
put (Reg reg) (Parser p) = Parser (In (L (PutRegister reg p)))

_join :: ParserR r (ParserR Id a) -> ParserR r a
_join = error "hahah nice try :)"

debug :: String -> ParserR r a -> ParserR r a
debug name (Parser p) = Parser (In (L (Debug name p)))