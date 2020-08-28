{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
module ParsleyParsers where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import Parsley
import Parsley.Combinator (atomic, oneOf, noneOf, eof)
import Parsley.Fold (skipMany, skipSome, sepBy, sepBy1, pfoldl1, chainl1)
import Parsley.Precedence (precedence, monolith, prefix, postfix, infixR, infixL)
import CommonFunctions
import Data.Char (isSpace, isUpper, digitToInt, isDigit)
import Data.Maybe (catMaybes)
import Text.Read (readMaybe)
import Control.Monad (liftM)

digit :: Parser Char Int
digit = code digitToInt <$> satisfy (code isDigit)

plus :: Parser Char (Int -> Int -> Int)
plus = char '+' $> code (+)

selectTest :: Parser Char (Either Int String)
selectTest = pure (code (Left 10))

showi :: Int -> String
showi = show

deriving instance Lift Pred

pred :: Parser Char Pred
pred = precedence (monolith [ prefix [atomic "!" $> code Not]
                            , infixR [atomic "&&" $> code And]])
                  ( atomic "t" $> code T
                <|> atomic "f" $> code F)

-- Brainfuck benchmark
deriving instance Lift BrainFuckOp

brainfuck :: Parser Char [BrainFuckOp]
brainfuck = whitespace *> bf <* eof
  where
    whitespace = skipMany (noneOf "<>+-[],.")
    lexeme p = p <* whitespace
    {-bf = many ( lexeme ((atomic ">" $> code RightPointer)
                    <|> (atomic "<" $> code LeftPointer)
                    <|> (atomic "+" $> code Increment)
                    <|> (atomic "-" $> code Decrement)
                    <|> (atomic "." $> code Output)
                    <|> (atomic "," $> code Input)
                    <|> (between (lexeme (atomic "[")) (atomic "]") (code Loop <$> bf))))-}
    bf = many (lexeme (match "><+-.,[" (lookAhead item) op empty))
    op '>' = item $> code RightPointer
    op '<' = item $> code LeftPointer
    op '+' = item $> code Increment
    op '-' = item $> code Decrement
    op '.' = item $> code Output
    op ',' = item $> code Input
    op '[' = between (lexeme item) (try (char ']')) (code Loop <$> bf)

-- Regex Benchmark
regex :: Parser Char Bool
regex = skipMany (aStarb *> aStarb) *> char 'a' $> code True <|> pure (code False)
  where
    aStarb = aStar *> char 'b'
    aStar = skipMany (char 'a')

-- Javascript
deriving instance Lift JSElement
deriving instance Lift JSStm
deriving instance Lift JSVar
deriving instance Lift JSExpr'
deriving instance Lift JSUnary
deriving instance Lift JSMember
deriving instance Lift JSCons
deriving instance Lift JSAtom

javascript :: Parser Char JSProgram
javascript = whitespace *> many element <* eof
  where
    element :: Parser Char JSElement
    element = keyword "function" *> liftA3 (code JSFunction) identifier (parens (commaSep identifier)) compound
          <|> code JSStm <$> stmt
    compound :: Parser Char JSCompoundStm
    compound = braces (many stmt)
    stmt :: Parser Char JSStm
    stmt = semi $> code JSSemi
       <|> keyword "if" *> liftA3 (code JSIf) parensExpr stmt (maybeP (keyword "else" *> stmt))
       <|> keyword "while" *> liftA2 (code JSWhile) parensExpr stmt
       <|> (keyword "for" *> parens
               (try (liftA2 (code JSForIn) varsOrExprs (keyword "in" *> expr))
            <|> liftA3 (code JSFor) (maybeP varsOrExprs <* semi) (optExpr <* semi) optExpr)
           <*> stmt)
       <|> keyword "break" $> code JSBreak
       <|> keyword "continue" $> code JSContinue
       <|> keyword "with" *> liftA2 (code JSWith) parensExpr stmt
       <|> keyword "return" *> (code JSReturn <$> optExpr)
       <|> code JSBlock <$> compound
       <|> code JSNaked <$> varsOrExprs
    varsOrExprs :: Parser Char (Either [JSVar] JSExpr)
    varsOrExprs = keyword "var" *> commaSep1 variable <+> expr
    variable :: Parser Char JSVar
    variable = liftA2 (code JSVar) identifier (maybeP (symbol '=' *> asgn))
    parensExpr :: Parser Char JSExpr
    parensExpr = parens expr
    optExpr :: Parser Char (Maybe JSExpr)
    optExpr = maybeP expr
    expr :: Parser Char JSExpr
    expr = commaSep1 asgn
    asgn :: Parser Char JSExpr'
    asgn = chainl1 condExpr (symbol '=' $> code JSAsgn)
    condExpr :: Parser Char JSExpr'
    condExpr = liftA2 (code jsCondExprBuild) expr' (maybeP ((symbol '?' *> asgn) <~> (symbol ':' *> asgn)))
    expr' :: Parser Char JSExpr'
    expr' = precedence (monolith
      [ prefix  [ operator "--" $> code jsDec, operator "++" $> code jsInc
                , operator "-" $> code jsNeg, operator "+" $> code jsPlus
                , operator "~" $> code jsBitNeg, operator "!" $> code jsNot ]
      , postfix [ operator "--" $> code jsDec, operator "++" $> code jsInc ]
      , infixL  [ operator "*" $> code JSMul, operator "/" $> code JSDiv
                , operator "%" $> code JSMod ]
      , infixL  [ operator "+" $> code JSAdd, operator "-" $> code JSSub ]
      , infixL  [ operator "<<" $> code JSShl, operator ">>" $> code JSShr ]
      , infixL  [ operator "<=" $> code JSLe, operator "<" $> code JSLt
                , operator ">=" $> code JSGe, operator ">" $> code JSGt ]
      , infixL  [ operator "==" $> code JSEq, operator "!=" $> code JSNe ]
      , infixL  [ try (operator "&") $> code JSBitAnd ]
      , infixL  [ operator "^" $> code JSBitXor ]
      , infixL  [ try (operator "|") $> code JSBitOr ]
      , infixL  [ operator "&&" $> code JSAnd ]
      , infixL  [ operator "||" $> code JSOr ]
      ])
      (code JSUnary <$> memOrCon)
    memOrCon :: Parser Char JSUnary
    memOrCon = keyword "delete" *> (code JSDel <$> member)
           <|> keyword "new" *> (code JSCons <$> con)
           <|> code JSMember <$> member
    con :: Parser Char JSCons
    con = liftA2 (code JSQual) (keyword "this" $> code "this") (dot *> conCall) <|> conCall
    conCall :: Parser Char JSCons
    conCall = identifier <**>
                (dot *> (([flip (code JSQual)]) <$> conCall)
             <|> ([flip (code JSConCall)]) <$> parens (commaSep asgn)
             <|> pure (makeQ (\name -> JSConCall name []) [||\name -> JSConCall name []||]))
    member :: Parser Char JSMember
    member = primaryExpr <**>
                (([flip (code JSCall)]) <$> parens (commaSep asgn)
             <|> ([flip (code JSIndex)]) <$> brackets expr
             <|> dot *> (([flip (code JSAccess)]) <$> member)
             <|> pure (code JSPrimExp))
    primaryExpr :: Parser Char JSAtom
    primaryExpr = code JSParens <$> parens expr
              <|> code JSArray <$> brackets (commaSep asgn)
              <|> code JSId <$> identifier
              <|> ([either (code JSInt) (code JSFloat)]) <$> naturalOrFloat
              <|> code JSString <$> stringLiteral
              <|> code JSTrue <$ keyword "true"
              <|> code JSFalse <$ keyword "false"
              <|> code JSNull <$ keyword "null"
              <|> code JSThis <$ keyword "this"

    -- Token Parsers
    space :: Parser Char ()
    space = void (satisfy (code isSpace))
    whitespace :: Parser Char ()
    whitespace = skipMany (spaces <|> oneLineComment <|> multiLineComment)
    keyword :: String -> Parser Char ()
    keyword s = try (string s *> notIdentLetter) *> whitespace
    operator :: String -> Parser Char ()
    operator op = try (string op *> notOpLetter) *> whitespace
    identifier :: Parser Char String
    identifier = try ((identStart <:> many identLetter) >?> code jsUnreservedName) <* whitespace
    naturalOrFloat :: Parser Char (Either Int Double)
    naturalOrFloat = natFloat <* whitespace--}code Left <$> (code read <$> some (oneOf ['0'..'9'])) <* whitespace

    -- Nonsense to deal with floats and ints
    natFloat :: Parser Char (Either Int Double)
    natFloat = char '0' *> zeroNumFloat <|> decimalFloat

    zeroNumFloat :: Parser Char (Either Int Double)
    zeroNumFloat = code Left <$> (hexadecimal <|> octal)
               <|> decimalFloat
               <|> (fromMaybeP (fractFloat <*> pure (code 0)) empty)
               <|> pure (code (Left 0))

    decimalFloat :: Parser Char (Either Int Double)
    decimalFloat = fromMaybeP (decimal <**> (option ([(.) (code Just) (code Left)]) fractFloat)) empty

    fractFloat :: Parser Char (Int -> Maybe (Either Int Double))
    fractFloat = makeQ f qf <$> fractExponent
      where
        f g x = liftM Right (g x)
        qf = [||\g x -> liftM Right (g x)||]

    fractExponent :: Parser Char (Int -> Maybe Double)
    fractExponent = makeQ f qf <$> fraction <*> option (code "") exponent'
                <|> makeQ g qg <$> exponent'
      where
        f fract exp n = readMaybe (show n ++ fract ++ exp)
        qf = [||\fract exp n -> readMaybe (show n ++ fract ++ exp)||]
        g exp n = readMaybe (show n ++ exp)
        qg = [||\exp n -> readMaybe (show n ++ exp)||]

    fraction :: Parser Char [Char]
    fraction = char '.' <:> some (oneOf ['0'..'9'])

    exponent' :: Parser Char [Char]
    exponent' = ([(:) (code 'e')]) <$> (oneOf "eE"
             *> (((code (:) <$> oneOf "+-") <|> pure (code id))
             <*> (code show <$> decimal)))

    decimal :: Parser Char Int
    decimal = number (code 10) (oneOf ['0'..'9'])
    hexadecimal = oneOf "xX" *> number (code 16) (oneOf (['a'..'f'] ++ ['A'..'F'] ++ ['0'..'9']))
    octal = oneOf "oO" *> number (code 8) (oneOf ['0'..'7'])

    number :: WQ Int -> Parser Char Char -> Parser Char Int
    number qbase digit = pfoldl1 (makeQ f qf) (code 0) digit
      where
        f x d = _val qbase * x + digitToInt d
        qf = [||\x d -> $$(_code qbase) * x + digitToInt d||]

    stringLiteral :: Parser Char String
    stringLiteral = code catMaybes <$> between (char '\"') (char '\"') (many stringChar) <* whitespace
    symbol :: Char -> Parser Char Char
    symbol c = try (char c) <* whitespace
    parens :: Parser Char a -> Parser Char a
    parens = between (symbol '(') (symbol ')')
    brackets :: Parser Char a -> Parser Char a
    brackets = between (symbol '[') (symbol ']')
    braces :: Parser Char a -> Parser Char a
    braces = between (symbol '{') (symbol '}')
    dot :: Parser Char Char
    dot = symbol '.'
    semi :: Parser Char Char
    semi = symbol ';'
    comma :: Parser Char Char
    comma = symbol ','
    commaSep :: Parser Char a -> Parser Char [a]
    commaSep p = sepBy p comma
    commaSep1 :: Parser Char a -> Parser Char [a]
    commaSep1 p = sepBy1 p comma

    -- Let bindings
    spaces :: Parser Char ()
    spaces = skipSome space

    oneLineComment :: Parser Char ()
    oneLineComment = void (atomic "//" *> skipMany (satisfy (makeQ (/= '\n') [||(/= '\n')||])))

    multiLineComment :: Parser Char ()
    multiLineComment =
      let inComment = void (atomic "*/")
                  <|> skipSome (noneOf "*") *> inComment
                  <|> char '*' *> inComment
      in atomic "/*" *> inComment

    identStart = satisfy (code jsIdentStart)
    identLetter = satisfy (code jsIdentLetter)
    notIdentLetter = notFollowedBy identLetter
    notOpLetter = notFollowedBy (oneOf "+-*/=<>!~&|.%^")

    escChrs :: [Char]
    escChrs = "abfntv\\\"'0123456789xo^ABCDEFGHLNRSUV"

    stringChar :: Parser Char (Maybe Char)
    stringChar = code Just <$> satisfy (code jsStringLetter) <|> stringEscape

    stringEscape :: Parser Char (Maybe Char)
    stringEscape = atomic "\\" *> (atomic "&" $> code Nothing
                              <|> spaces *> atomic "\\" $> code Nothing
                              <|> code Just <$> escapeCode)

    escapeCode :: Parser Char Char
    escapeCode = match escChrs (oneOf escChrs) escCode empty
      where
        escCode 'a' = pure (code ('\a'))
        escCode 'b' = pure (code ('\b'))
        escCode 'f' = pure (code ('\f'))
        escCode 'n' = pure (code ('\n'))
        escCode 't' = pure (code ('\t'))
        escCode 'v' = pure (code ('\v'))
        escCode '\\' = pure (code ('\\'))
        escCode '"' = pure (code ('"'))
        escCode '\'' = pure (code ('\''))
        escCode '^' = makeQ (\c -> toEnum (fromEnum c - fromEnum 'A' + 1)) [||\c -> toEnum (fromEnum c - fromEnum 'A' + 1)||] <$> satisfy (code isUpper)
        escCode 'A' = atomic "CK" $> code ('\ACK')
        escCode 'B' = atomic "S" $> code ('\BS') <|> atomic "EL" $> code ('\BEL')
        escCode 'C' = atomic "R" $> code ('\CR') <|> atomic "AN" $> code ('\CAN')
        escCode 'D' = atomic "C" *> (atomic "1" $> code ('\DC1')
                             <|> atomic "2" $> code ('\DC2')
                             <|> atomic "3" $> code ('\DC3')
                             <|> atomic "4" $> code ('\DC4'))
               <|> atomic "EL" $> code ('\DEL')
               <|> atomic "LE" $> code ('\DLE')
        escCode 'E' = atomic "M" $> code ('\EM')
               <|> atomic "T" *> (atomic "X" $> code ('\ETX')
                             <|> atomic "B" $> code ('\ETB'))
               <|> atomic "SC" $> code ('\ESC')
               <|> atomic "OT" $> code ('\EOT')
               <|> atomic "NQ" $> code ('\ENQ')
        escCode 'F' = atomic "F" $> code ('\FF') <|> atomic "S" $> code ('\FS')
        escCode 'G' = atomic "S" $> code ('\GS')
        escCode 'H' = atomic "T" $> code ('\HT')
        escCode 'L' = atomic "F" $> code ('\LF')
        escCode 'N' = atomic "UL" $> code ('\NUL') <|> atomic "AK" $> code ('\NAK')
        escCode 'R' = atomic "S" $> code ('\RS')
        escCode 'S' = atomic "O" *> option (code ('\SO')) (atomic "H" $> code ('\SOH'))
               <|> atomic "I" $> code ('\SI')
               <|> atomic "P" $> code ('\SP')
               <|> atomic "TX" $> code ('\STX')
               <|> atomic "YN" $> code ('\SYN')
               <|> atomic "UB" $> code ('\SUB')
        escCode 'U' = atomic "S" $> code ('\US')
        escCode 'V' = atomic "T" $> code ('\VT')
        -- TODO numeric
        escCode _ = empty--error "numeric escape codes not supported"

nandlang :: Parser Char ()
nandlang = whitespace *> skipMany funcdef <* eof
  where
    index :: Parser Char ()
    index = brackets nat
    identifier :: Parser Char ()
    identifier = try (identStart *> skipMany identLetter) *> whitespace--try ((identStart <:> many identLetter) >?> code nandUnreservedName) *> whitespace
    variable :: Parser Char ()
    variable = identifier *> optional index

    literal :: Parser Char ()
    literal = bit <|> charLit

    keyword :: String -> Parser Char ()
    keyword s = try (string s *> notIdentLetter) *> whitespace

    identStart = satisfy (code nandIdentStart)
    identLetter = satisfy (code nandIdentLetter)
    notIdentLetter = notFollowedBy identLetter

    bit :: Parser Char ()
    bit = (char '0' <|> char '1') *> whitespace

    nat :: Parser Char ()
    nat = decimal

    charLit :: Parser Char ()
    charLit = between (char '\'') (symbol '\'') charChar

    charChar :: Parser Char ()
    charChar = void (satisfy (code jsStringLetter)) <|> esc

    esc :: Parser Char ()
    esc = char '\\' *> void (oneOf "0tnvfr")

    expr :: Parser Char ()
    expr = nandexpr *> skipMany (symbol '!' *> nandexpr)

    nandexpr :: Parser Char ()
    nandexpr = literal <|> funccallOrVar

    funccallOrVar :: Parser Char ()
    funccallOrVar = identifier *> optional (parens exprlist <|> index)

    exprlist = commaSep expr
    exprlist1 = commaSep1 expr
    varlist = commaSep variable
    varlist1 = commaSep1 variable

    funcparam = varlist *> optional (symbol ':' *> varlist)
    varstmt = optional (keyword "var") *> varlist1 *> symbol '=' *> exprlist1 <* semi
    ifstmt = keyword "if" *> expr *> block *> optional (keyword "else" *> block)
    whilestmt = keyword "while" *> expr *> block
    statement = ifstmt <|> whilestmt <|> try varstmt <|> expr <* semi
    block = braces (skipMany statement)
    funcdef = keyword "function" *> identifier *> parens funcparam *> block

    decimal :: Parser Char ()
    decimal = number (oneOf ['0'..'9'])
    hexadecimal = oneOf "xX" *> number (oneOf (['a'..'f'] ++ ['A'..'F'] ++ ['0'..'9']))
    octal = oneOf "oO" *> number (oneOf ['0'..'7'])
    number :: Parser Char a -> Parser Char ()
    number digit = skipSome digit

    symbol :: Char -> Parser Char Char
    symbol c = char c <* whitespace
    parens :: Parser Char a -> Parser Char a
    parens = between (symbol '(') (symbol ')')
    brackets :: Parser Char a -> Parser Char a
    brackets = between (symbol '[') (symbol ']')
    braces :: Parser Char a -> Parser Char a
    braces = between (symbol '{') (symbol '}')
    semi :: Parser Char Char
    semi = symbol ';'
    comma :: Parser Char Char
    comma = symbol ','
    commaSep :: Parser Char a -> Parser Char ()
    commaSep p = optional (commaSep1 p)
    commaSep1 :: Parser Char a -> Parser Char ()
    commaSep1 p = p *> skipMany (comma *> p)

    space :: Parser Char ()
    space = void (satisfy (code isSpace))
    whitespace :: Parser Char ()
    whitespace = skipMany (spaces <|> oneLineComment)
    spaces :: Parser Char ()
    spaces = skipSome space
    oneLineComment :: Parser Char ()
    oneLineComment = void (atomic "//" *> skipMany (satisfy (makeQ (/= '\n') [||(/= '\n')||])))
