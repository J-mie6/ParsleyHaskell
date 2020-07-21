{-# OPTIONS_GHC -fplugin=LiftPlugin #-}
{-# LANGUAGE AllowAmbiguousTypes,
             MultiParamTypeClasses,
             TypeApplications,
             TypeFamilies #-}
module Parsley (
    module Parsley,
    module Core,
    module THUtils,
    Lift(..)
  ) where

import Prelude hiding             (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), (>>), sequence, traverse, repeat, readFile)
import Data.Function              (fix)
import Data.Kind                  (Type)
import Data.Text.IO               (readFile)
import Debug.Trace                (trace)
import Language.Haskell.TH.Syntax (Lift(..))
import Parsley.Backend            (codeGen, Input, eval, prepare)
import Parsley.Core
import Parsley.Frontend           (compile)
import System.Console.Pretty      (color, style, Color(Red), Style(Bold, Underline, Italic))

import Parsley.Core as Core hiding     (_pure, _satisfy, _conditional, _join)
import Parsley.Common.Utils as THUtils (code, Quapplicative(..), WQ, Code)

class (ParserOps rep, Rep rep ~ rep) => Uncode rep where uncode :: WQ a -> rep a
instance Uncode WQ where uncode = id
instance Uncode Id where uncode = Id . _val

class ParserOps rep where
  type Rep rep :: Type -> Type
  pure :: rep a -> ParserR (Rep rep) a
  satisfy :: rep (Char -> Bool) -> ParserR (Rep rep) Char
  conditional :: [(rep (a -> Bool), ParserR (Rep rep) b)] -> ParserR (Rep rep) a -> ParserR (Rep rep) b -> ParserR (Rep rep) b

instance ParserOps WQ where
  type Rep WQ = WQ
  pure = pure . BLACK
  satisfy = satisfy . BLACK
  conditional cs p def = conditional (map (\(f, t) -> (BLACK f, t)) cs) p def

instance ParserOps (Defunc r) where
  type Rep (Defunc r) = r
  pure = _pure
  satisfy = _satisfy
  conditional = _conditional

instance {-# INCOHERENT #-} ParserOps Id where
  type Rep Id = Id
  pure = undefined
  satisfy = undefined
  conditional = undefined

fmap :: (ParserOps rep, r ~ Rep rep) => rep (a -> b) -> ParserR r a -> ParserR r b
fmap f = (pure f <*>)

infixl 4 <$>
(<$>) :: (ParserOps rep, r ~ Rep rep) => rep (a -> b) -> ParserR r a -> ParserR r b
(<$>) = fmap

void :: ParserR r a -> ParserR r ()
void p = p *> unit

infixl 4 <$
(<$) :: (ParserOps rep, r ~ Rep rep) => rep b -> ParserR r a -> ParserR r b
x <$ p = p *> pure x

infixl 4 $>
($>) :: (ParserOps rep, r ~ Rep rep) => ParserR r a -> rep b -> ParserR r b
($>) = flip (<$)

infixl 4 <&>
(<&>) :: (ParserOps rep, r ~ Rep rep) => ParserR r a -> rep (a -> b) -> ParserR r b
(<&>) = flip fmap

liftA2 :: (ParserOps rep, r ~ Rep rep) => rep (a -> b -> c) -> ParserR r a -> ParserR r b -> ParserR r c
liftA2 f p q = f <$> p <*> q

liftA3 :: (ParserOps rep, r ~ Rep rep) => rep (a -> b -> c -> d) -> ParserR r a -> ParserR r b -> ParserR r c -> ParserR r d
liftA3 f p q r = f <$> p <*> q <*> r

join :: ParserR r (ParserR Id a) -> ParserR r a
join = trace joinWarning $ _join
  where
    -- TODO HasCallStack?
    joinWarning = unlines [ unwords [color Red "WARNING: `join` is", color Red (style Bold "VERY"), color Red "expensive..."]
                          , "Make sure you know what you're doing:"
                          , unwords ["    legitimate uses of `join` are", style Italic "very rare"]
                          , unwords ["    if possible use registers/`bind` and/or selectives, or if", style Underline "absolutely necessary" ++ ",", "make sure you minimise the size of the parserR r inside"]
                          , "This warning may be surpressed by hiding `join` from Parsley and importing Parsley.ReallyVerySlow (join)" ]

many :: ParserR r a -> ParserR r [a]
many = pfoldr CONS EMPTY

manyN :: Int -> ParserR r a -> ParserR r [a]
manyN n p = foldr (const (p <:>)) (many p) [1..n]

some :: ParserR r a -> ParserR r [a]
some = manyN 1

skipMany :: ParserR r a -> ParserR r ()
--skipMany p = let skipManyp = p *> skipManyp <|> unit in skipManyp
skipMany = void . pfoldl CONST UNIT -- the void here will encourage the optimiser to recognise that the register is unused

skipManyN :: Int -> ParserR r a -> ParserR r ()
skipManyN n p = foldr (const (p *>)) (skipMany p) [1..n]

skipSome :: ParserR r a -> ParserR r ()
skipSome = skipManyN 1

infixl 3 <+>
(<+>) :: Uncode r => ParserR r a -> ParserR r b -> ParserR r (Either a b)
p <+> q = uncode (code Left) <$> p <|> uncode (code Right) <$> q

sepBy :: ParserR r a -> ParserR r b -> ParserR r [a]
sepBy p sep = option EMPTY (sepBy1 p sep)

sepBy1 :: ParserR r a -> ParserR r b -> ParserR r [a]
sepBy1 p sep = p <:> many (sep *> p)

endBy :: ParserR r a -> ParserR r b -> ParserR r [a]
endBy p sep = many (p <* sep)

endBy1 :: ParserR r a -> ParserR r b -> ParserR r [a]
endBy1 p sep = some (p <* sep)

sepEndBy :: ParserR r a -> ParserR r b -> ParserR r [a]
sepEndBy p sep = option EMPTY (sepEndBy1 p sep)

{-sepEndBy1 :: ParserR r a -> ParserR r b -> ParserR r [a]
sepEndBy1 p sep =
  let seb1 = p <**> (sep *> (FLIP_H CONS <$> option EMPTY seb1)
                 <|> pure (APP_H (FLIP_H CONS) EMPTY))
  in seb1-}

sepEndBy1 :: ParserR r a -> ParserR r b -> ParserR r [a]
sepEndBy1 p sep = newRegister_ ID $ \acc ->
  let go = modify acc (COMPOSE_H (FLIP_H COMPOSE) CONS <$> p)
         *> (sep *> (go <|> get acc) <|> get acc)
  in go <*> pure EMPTY

manyTill :: ParserR r a -> ParserR r b -> ParserR r [a]
manyTill p end = let go = end $> EMPTY <|> p <:> go in go

someTill :: ParserR r a -> ParserR r b -> ParserR r [a]
someTill p end = notFollowedBy end *> (p <:> manyTill p end)

-- Additional Combinators
{-# INLINE (<:>) #-}
infixl 4 <:>
(<:>) :: ParserR r a -> ParserR r [a] -> ParserR r [a]
(<:>) = liftA2 CONS

infixl 4 <**>
(<**>) :: ParserR r a -> ParserR r (a -> b) -> ParserR r b
(<**>) = liftA2 (FLIP_H APP)

unit :: ParserR r ()
unit = pure UNIT

infixl 4 <~>
(<~>) :: Uncode r => ParserR r a -> ParserR r b -> ParserR r (a, b)
(<~>) = liftA2 (uncode (code (,)))

infixl 4 <~
(<~) :: ParserR r a -> ParserR r b -> ParserR r a
(<~) = (<*)

infixl 4 ~>
(~>) :: ParserR r a -> ParserR r b -> ParserR r b
(~>) = (*>)

infixl 1 >>
(>>) :: ParserR r a -> ParserR r b -> ParserR r b
(>>) = (*>)

-- Auxillary functions
sequence :: [ParserR r a] -> ParserR r [a]
sequence = foldr (<:>) (pure EMPTY)

traverse :: (a -> ParserR r b) -> [a] -> ParserR r [b]
traverse f = sequence . map f

string :: String -> ParserR r String
string = traverse char

oneOf :: Uncode r => [Char] -> ParserR r Char
oneOf cs = satisfy (uncode (makeQ (flip elem cs) [||\c -> $$(ofChars cs [||c||])||]))

noneOf :: Uncode r => [Char] -> ParserR r Char
noneOf cs = satisfy (uncode (makeQ (not . flip elem cs) [||\c -> not $$(ofChars cs [||c||])||]))

ofChars :: [Char] -> Code Char -> Code Bool
ofChars = foldr (\c rest qc -> [|| c == $$qc || $$(rest qc) ||]) (const [||False||])

token :: String -> ParserR r String
token = try . string

eof :: Uncode r => ParserR r ()
eof = notFollowedBy item

more :: Uncode r => ParserR r ()
more = lookAhead (void item)

repeat :: Int -> ParserR r a -> ParserR r [a]
repeat n p = traverse (const p) [1..n]

between :: ParserR r o -> ParserR r c -> ParserR r a -> ParserR r a
between open close p = open *> p <* close

-- Parsing Primitives
char :: Char -> ParserR r Char
char c = satisfy (EQ_H (CHAR c)) $> CHAR c

item :: Uncode r => ParserR r Char
item = satisfy (APP_H CONST (BLACK (uncode (code True))))

{-notFollowedBy :: ParserR r a -> ParserR r ()
notFollowedBy p = newRegister_ (code True) $ \ok ->
     optional (try (lookAhead p *> put_ ok (code False)))
  *> get ok <?:> (unit, empty)-}

-- Composite Combinators
optionally :: (ParserOps rep, r ~ Rep rep) => ParserR r a -> rep b -> ParserR r b
optionally p x = p $> x <|> pure x

optional :: ParserR r a -> ParserR r ()
optional = flip optionally UNIT

option :: (ParserOps rep, r ~ Rep rep) => rep a -> ParserR r a -> ParserR r a
option x p = p <|> pure x

choice :: [ParserR r a] -> ParserR r a
choice = foldr (<|>) empty

constp :: ParserR r a -> ParserR r (b -> a)
constp = (CONST <$>)

infixl 4 <?:>
(<?:>) :: ParserR r Bool -> (ParserR r a, ParserR r a) -> ParserR r a
cond <?:> (p, q) = predicate ID cond p q

predicate :: (ParserOps rep, r ~ Rep rep) => rep (a -> Bool) -> ParserR r a -> ParserR r b -> ParserR r b -> ParserR r b
predicate cond p t e = conditional [(cond, t)] p e

filteredBy :: (ParserOps rep, Uncode r, Rep rep ~ r) => ParserR r a -> rep (a -> Bool) -> ParserR r a
filteredBy p f = p >??> pure f

infixl 4 >?>
(>?>) :: (ParserOps rep, Uncode r, Rep rep ~ r) => ParserR r a -> rep (a -> Bool) -> ParserR r a
(>?>) = filteredBy

infixl 4 >??>
(>??>) :: Uncode r => ParserR r a -> ParserR r (a -> Bool) -> ParserR r a
px >??> pf = select (liftA2 (uncode (makeQ g qg)) pf px) empty
  where
    g f x = if f x then Right x else Left ()
    qg = [||\f x -> if f x then Right x else Left ()||]

match :: (Eq a, Lift a, Uncode r) => [a] -> ParserR r a -> (a -> ParserR r b) -> ParserR r b -> ParserR r b
match vs p f = _conditional (map (\v -> (EQ_H (BLACK (uncode (code v))), f v)) vs) p

infixl 1 ||=
(||=) :: (Enum a, Bounded a, Eq a, Lift a, Uncode r) => ParserR r a -> (a -> ParserR r b) -> ParserR r b
p ||= f = match [minBound..maxBound] p f empty

when :: ParserR r Bool -> ParserR r () -> ParserR r ()
when p q = p <?:> (q, unit)

while :: ParserR r Bool -> ParserR r ()
while x = fix (when x)

select :: ParserR r (Either a b) -> ParserR r (a -> b) -> ParserR r b
select p q = branch p q (pure ID)

fromMaybeP :: Uncode r => ParserR r (Maybe a) -> ParserR r a -> ParserR r a
fromMaybeP pm px = select (uncode (makeQ (maybe (Left ()) Right) [||maybe (Left ()) Right||]) <$> pm) (constp px)

maybeP :: Uncode r => ParserR r a -> ParserR r (Maybe a)
maybeP p = option (uncode (makeQ Nothing [||Nothing||])) (uncode (code Just) <$> p)

-- Stateful Parsers
newRegister_ :: (ParserOps rep, r ~ Rep rep) => rep a -> (forall r1. Reg r1 a -> ParserR r b) -> ParserR r b
newRegister_ x = newRegister (pure x)

put_ :: (ParserOps rep, r ~ Rep rep) => Reg r1 a -> rep a -> ParserR r ()
put_ r = put r . pure

gets :: Reg r1 a -> ParserR r (a -> b) -> ParserR r b
gets r p = p <*> get r

gets_ :: (ParserOps rep, r ~ Rep rep) => Reg r1 a -> rep (a -> b) -> ParserR r b
gets_ r = gets r . pure

modify :: Reg r1 a -> ParserR r (a -> a) -> ParserR r ()
modify r p = put r (gets r p)

modify_ :: (ParserOps rep, r ~ Rep rep) => Reg r1 a -> rep (a -> a) -> ParserR r ()
modify_ r = modify r . pure

move :: Reg r1 a -> Reg r2 a -> ParserR r ()
move dst src = put dst (get src)

bind :: ParserR r a -> (ParserR r a -> ParserR r b) -> ParserR r b
bind p f = newRegister p (f . get)

local :: Reg r1 a -> ParserR r a -> ParserR r b -> ParserR r b
local r p q = bind (get r) $ \x -> put r p
                                *> q
                                <* put r x

swap :: Reg r1 a -> Reg r2 a -> ParserR r ()
swap r1 r2 = bind (get r1) $ \x -> move r1 r2
                                *> put r2 x

rollback :: Reg r1 a -> ParserR r b -> ParserR r b
rollback r p = bind (get r) $ \x -> p <|> put r x *> empty

for :: forall r a. ParserR r a -> ParserR r (a -> Bool) -> ParserR r (a -> a) -> ParserR r () -> ParserR r ()
for init cond step body =
  newRegister init $ \i ->
    let cond' :: ParserR r Bool
        cond' = gets i cond
    in when cond' (while (body *> modify i step *> cond'))

-- Iterative Parsers
{-chainPre :: ParserR r (a -> a) -> ParserR r a -> ParserR r a
chainPre op p = newRegister_ ID $ \acc ->
  let go = modify acc (FLIP_H COMPOSE <$> op) *> go
       <|> get acc
  in go <*> p -}

{-chainPost :: ParserR r a -> ParserR r (a -> a) -> ParserR r a
chainPost p op = newRegister p $ \acc ->
  let go = modify acc op *> go
       <|> get acc
  in go-}

chainl1' :: (ParserOps rep, r ~ Rep rep)=> rep (a -> b) -> ParserR r a -> ParserR r (b -> a -> b) -> ParserR r b
chainl1' f p op = chainPost (f <$> p) (FLIP <$> op <*> p)

chainl1 :: ParserR r a -> ParserR r (a -> a -> a) -> ParserR r a
chainl1 = chainl1' ID

chainr1' :: (ParserOps rep, r ~ Rep rep) => rep (a -> b) -> ParserR r a -> ParserR r (a -> b -> b) -> ParserR r b
chainr1' f p op = newRegister_ ID $ \acc ->
  let go = bind p $ \x ->
           modify acc (FLIP_H COMPOSE <$> (op <*> x)) *> go
       <|> f <$> x
  in go <**> get acc

chainr1 :: ParserR r a -> ParserR r (a -> a -> a) -> ParserR r a
chainr1 = chainr1' ID

chaint' :: (ParserOps rep, r ~ Rep rep) => rep (a -> b) -> ParserR r a -> ParserR r (ParserR Id (a -> a -> b -> b)) -> ParserR r b
chaint' f p op = newRegister_ ID $ \acc ->
  let go = bind p $ \x ->
           modify acc (FLIP_H COMPOSE <$> (bind op (\g -> p <**> (_join g <*> x)))) *> go
       <|> f <$> x
  in go <**> get acc

chaint :: ParserR r a -> ParserR r (ParserR Id (a -> a -> a -> a)) -> ParserR r a
chaint = chaint' ID

chainr :: (ParserOps rep, r ~ Rep rep) => ParserR r a -> ParserR r (a -> a -> a) -> rep a -> ParserR r a
chainr p op x = option x (chainr1 p op)

chainl :: (ParserOps rep, r ~ Rep rep) => ParserR r a -> ParserR r (a -> a -> a) -> rep a -> ParserR r a
chainl p op x = option x (chainl1 p op)

pfoldr :: (ParserOps repf, ParserOps repk, Rep repf ~ Rep repk, r ~ Rep repf) => repf (a -> b -> b) -> repk b -> ParserR r a -> ParserR r b
pfoldr f k p = chainPre (f <$> p) (pure k)

pfoldr1 :: (ParserOps repf, ParserOps repk, Rep repf ~ Rep repk, r ~ Rep repf) => repf (a -> b -> b) -> repk b -> ParserR r a -> ParserR r b
pfoldr1 f k p = f <$> p <*> pfoldr f k p

pfoldl :: (ParserOps repf, ParserOps repk, Rep repf ~ Rep repk, r ~ Rep repf)  => repf (b -> a -> b) -> repk b -> ParserR r a -> ParserR r b
pfoldl f k p = chainPost (pure k) ((FLIP <$> pure f) <*> p)

pfoldl1 :: (ParserOps repf, ParserOps repk, Rep repf ~ Rep repk, r ~ Rep repf) => repf (b -> a -> b) -> repk b -> ParserR r a -> ParserR r b
pfoldl1 f k p = chainPost (f <$> pure k <*> p) ((FLIP <$> pure f) <*> p)

data Level r a b = InfixL  [ParserR r (b -> a -> b)]                   (Defunc r (a -> b))
                 | InfixR  [ParserR r (a -> b -> b)]                   (Defunc r (a -> b))
                 | Prefix  [ParserR r (b -> b)]                        (Defunc r (a -> b))
                 | Postfix [ParserR r (b -> b)]                        (Defunc r (a -> b))
                 | Ternary [ParserR r (ParserR Id (a -> a -> b -> b))] (Defunc r (a -> b))

class Monolith r a b c where
  infixL  :: [ParserR r (b -> a -> b)]                   -> c
  infixR  :: [ParserR r (a -> b -> b)]                   -> c
  prefix  :: [ParserR r (b -> b)]                        -> c
  postfix :: [ParserR r (b -> b)]                        -> c
  ternary :: [ParserR r (ParserR Id (a -> a -> b -> b))] -> c

instance x ~ a => Monolith r x a (Level r a a) where
  infixL  = flip InfixL ID
  infixR  = flip InfixR ID
  prefix  = flip Prefix ID
  postfix = flip Postfix ID
  ternary = flip Ternary ID

instance {-# INCOHERENT #-} x ~ (WQ (a -> b) -> Level WQ a b) => Monolith WQ a b x where
  infixL  ops = InfixL ops . BLACK
  infixR  ops = InfixR ops . BLACK
  prefix  ops = Prefix ops . BLACK
  postfix ops = Postfix ops . BLACK
  ternary ops = Ternary ops . BLACK

data Prec r a b where
  NoLevel :: Prec r a a
  Level :: Level r a b -> Prec r b c -> Prec r a c

monolith :: [Level r a a] -> Prec r a a
monolith = foldr Level NoLevel

precedence :: Prec r a b -> ParserR r a -> ParserR r b
precedence NoLevel atom = atom
precedence (Level lvl lvls) atom = precedence lvls (level lvl atom)
  where
    level (InfixL ops wrap) atom  = chainl1' wrap atom (choice ops)
    level (InfixR ops wrap) atom  = chainr1' wrap atom (choice ops)
    level (Prefix ops wrap) atom  = chainPre (choice ops) (wrap <$> atom)
    level (Postfix ops wrap) atom = chainPost (wrap <$> atom) (choice ops)
    level (Ternary ops wrap) atom = chaint' wrap atom (choice ops)

runParser :: Input input => Parser a -> Code (input -> Maybe a)
runParser p = [||\input -> $$(eval (prepare [||input||]) (compile p codeGen))||]

parseFromFile :: Parser a -> Code (FilePath -> IO (Maybe a))
parseFromFile p = [||\filename -> do input <- readFile filename; return ($$(runParser p) (Text16 input))||]
