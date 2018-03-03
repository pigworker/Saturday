{-# LANGUAGE OverloadedStrings #-}

module R where

import Data.Attoparsec.Text as P
import Data.Text as T
import Control.Applicative
import Data.Char

data RC
  = At A
  | Vd
  | RC :. RC
  | In RC
  | Ld A RC
  | Em RE

data RE
  = A :^ Int
  | RE :$ RC
  | RC :< RC

type A = Text

instance Show RC where
  show = T.unpack . tC

instance Show RE where
  show = T.unpack . tE

tC :: RC -> Text
tC (At a)         = a
tC Vd             = "()"
tC (In (c :. d))  = T.concat ["[", tC c, tD d, "]"]
tC (In d)         = T.concat ["[", tD d, "]"]
tC (Ld x c)       = T.concat ["\\", x, " ", tC c]
tC (Em e)         = T.concat ["{", tE e, "}"]
tC (c :. d)       = T.concat ["(", tC c, tD d, ")"]

tD :: RC -> Text
tD Vd         = ""
tD (c :. d)   = T.concat [" ", tC c, tD d]
tD c          = T.concat [", ", tC c]

tE :: RE -> Text
tE (x :^ 0) = x
tE (x :^ i) = T.concat [x, "^", T.pack (show i)]
tE (e :$ c) = T.concat [tE e, " ", tC c]
tE (c :< d) = T.concat ["{", tC c, " : ", tC d, "}"]

pC :: P.Parser RC -- assumes leading space has been consumed; leaves trailing space
pC = id <$ P.char '('   <* skipSpace <*> pD <* skipSpace <* P.char ')'
 <|> In <$ P.char '['   <* skipSpace <*> pD <* skipSpace <* P.char ']'
 <|> Em <$ P.char '{'   <* skipSpace <*> pE <* skipSpace <* P.char '}'
 <|> Ld <$ P.char '\\'  <* skipSpace <*> pA <* skipSpace <*> pC
 <|> At <$> pA

pD :: P.Parser RC
pD = id <$ P.char ',' <* skipSpace <*> pC
 <|> (:.) <$> pC <* skipSpace <*> pD
 <|> pure Vd

pA :: P.Parser A
pA = takeWhile1 $ \ c ->
  isAlpha c || isDigit c || elem c ['_','-','<','=','>','*','\'']

pE :: P.Parser RE
pE = pH >>= pM

pH :: P.Parser RE
pH = (:<) <$ P.char '{' <* skipSpace <*> pC <* skipSpace <*
             P.char ':' <* skipSpace <*> pC <* skipSpace <*
             P.char '}'
 <|> (:^) <$> pA <*> (id <$ P.char '^' <*> decimal <|> pure 0)

pM :: RE -> P.Parser RE
pM e = (((e :$) <$ skipSpace <*> pC) >>= pM) <|> pure e
