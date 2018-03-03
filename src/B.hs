{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
    GeneralizedNewtypeDeriving #-}

module B where

import Data.Bits
import Control.Arrow ((***))

data Bwd x = B0 | Bwd x :\ x deriving (Show, Eq, Functor, Foldable, Traversable)

instance Monoid (Bwd x) where
  mempty = B0
  mappend xz B0 = xz
  mappend xz (yz :\ y) = mappend xz yz :\ y

blen :: Bwd x -> Int
blen B0 = 0
blen (xz :\ _) = 1 + blen xz

newtype OPE = B Integer deriving (Show, Eq, Bits)

(<\) :: OPE -> Bool -> OPE
B i <\ False  = B (shiftL i 1)
B i <\ True   = B (shiftL i 1 .|. bit 0)

os, o' :: OPE -> OPE
os = (<\ True)
o' = (<\ False)

bout :: OPE -> (OPE, Bool)
bout (B i) = (B (shiftR i 1), testBit i 0)

bouts :: Int -> OPE -> (OPE, OPE)
bouts n (B i) = (B (shiftR i n), (B (i .&. (2 ^ n - 1))))

oe, oi :: OPE
oe = B 0
oi = B (-1)

(<<) :: OPE -> OPE -> OPE
ai << B (-1) = ai
ai << B 0    = oe
B (-1) << bi = bi
B 0    << bi = oe
ai << bi     = case bout bi of
  (bi, False)  -> o' (ai << bi)
  (bi, True)   -> case bout ai of
    (ai, a) -> (ai << bi) <\ a

(<?) :: OPE -> Int -> Int
B (-1) <? n = n
B 0    <? n = 0
bi     <? 0 = 0
bi     <? m = if b then n + 1 else n where
  (ai, b) = bout bi
  n = ai <? (m - 1)

(<??) :: OPE -> Bwd x -> Bwd x
B (-1) <?? xz = xz
B 0    <?? xz = B0
bi     <?? B0 = B0
bi     <?? (xz :\ x) = if b then yz :\ x else yz where
  (ai, b) = bout bi
  yz = ai <?? xz

data Re x = x :^ OPE deriving Show

instance Functor Re where
  fmap f (t :^ bi) = f t :^ bi

(^<<) :: Re t -> OPE -> Re t
(t :^ ai) ^<< bi = t :^ (ai << bi)

kR :: x -> Re x
kR x = x :^ oe

cop :: OPE -> OPE -> (OPE, OPE)
cop (B (-1)) bi = (oi, bi)
cop ai (B (-1)) = (ai, oi)
cop (B 0)    bi = (oe, oi)
cop ai    (B 0) = (oi, oe)
cop ai       bi = case (bout ai, bout bi) of
  ((ai, a), (bi, b)) ->
    (if a || b then (<\ a) *** (<\ b) else id) (cop ai bi)

type PR s t = (Re s, Re t)

pR :: Re s -> Re t -> Re (PR s t)
pR (s :^ ai) (t :^ bi) = (s :^ ai', t :^ bi') :^ (ai .|. bi) where
  (ai', bi') = cop ai bi

xR :: Int -> Re ()
xR i = () :^ B (bit i)

data Bn t =  (Int, OPE) :\\ t deriving Show
(\\) :: Int -> Re t -> Re (Bn t)
n \\ (t :^ ci) = ((n, bi) :\\ t) :^ ai where (ai, bi) = bouts n ci

data Sp x = S0 | SZ (PR (Sp x) x) deriving Show

(-\) :: Re (Sp x) -> Re x -> Re (Sp x)
xz -\ x = fmap SZ (pR xz x)

unSp :: Re (Sp x) -> Bwd (Re x)
unSp (S0 :^ _) = B0
unSp (SZ (xz, x) :^ ci) = unSp (xz ^<< ci) :\ (x ^<< ci)
