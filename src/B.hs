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

type OPE = Integer -- it used to be a newtype deriving (Show, Eq, Bits)

(<\) :: OPE -> Bool -> OPE
i <\ False  = shiftL i 1
i <\ True   = shiftL i 1 .|. bit 0

os, o' :: OPE -> OPE
os = (<\ True)
o' = (<\ False)

bout :: OPE -> (OPE, Bool)
bout i = (shiftR i 1, testBit i 0)

bouts :: Int -> OPE -> (OPE, OPE)
bouts n i = (shiftR i n, i .&. (2 ^ n - 1))

bins :: OPE -> Int -> OPE -> OPE
bins ai n bi = shiftL ai n .|. (bi .&. (2 ^ n - 1))

qOPE :: Int -> OPE -> OPE -> Bool
qOPE n i j = (i .&. m) == (j .&. m) where m = 2 ^ n - 1

oe, oi :: OPE
oe = 0
oi = (-1)

(<<) :: OPE -> OPE -> OPE
ai << (-1) = ai
ai << 0    = oe
(-1) << bi = bi
0    << bi = oe
ai << bi     = case bout bi of
  (bi, False)  -> o' (ai << bi)
  (bi, True)   -> case bout ai of
    (ai, a) -> (ai << bi) <\ a

(<?) :: OPE -> Int -> Int
(-1) <? n = n
0    <? n = 0
bi   <? 0 = 0
bi   <? m = if b then n + 1 else n where
  (ai, b) = bout bi
  n = ai <? (m - 1)

(<??) :: OPE -> Bwd x -> Bwd x
(-1) <?? xz = xz
0    <?? xz = B0
bi   <?? B0 = B0
bi   <?? (xz :\ x) = if b then yz :\ x else yz where
  (ai, b) = bout bi
  yz = ai <?? xz

data Re x = x :^ OPE deriving Show

instance Functor Re where
  fmap f (t :^ bi) = f t :^ bi

(^<<) :: Re t -> OPE -> Re t
(t :^ ai) ^<< bi = t :^ (ai << bi)

kR :: x -> Re x
kR x = x :^ oe

jR :: Re (Re t) -> Re t
jR ((t :^ ai) :^ bi) = t :^ (ai << bi)

psh :: OPE -> OPE -> (OPE, OPE)
psh (-1) bi = (oi, bi)
psh ai (-1) = (ai, oi)
psh 0    bi = (oe, oi)
psh ai    0 = (oi, oe)
psh ai   bi = case (bout ai, bout bi) of
  ((ai, a), (bi, b)) ->
    (if a || b then (<\ a) *** (<\ b) else id) (psh ai bi)

type PR s t = (Re s, Re t)

pR :: Re s -> Re t -> Re (PR s t)
pR (s :^ ai) (t :^ bi) = (s :^ ai', t :^ bi') :^ (ai .|. bi) where
  (ai', bi') = psh ai bi

prjR :: Re (PR s t) -> (Re s, Re t)
prjR ((s, t) :^ ci) = (s ^<< ci, t ^<< ci)

xR :: Int -> Re ()
xR i = () :^ bit i

data Bn t =  (Int, OPE) :\\ t deriving Show
(\\) :: Int -> Re t -> Re (Bn t)
n \\ (t :^ ci) = ((n, bi) :\\ t) :^ ai where (ai, bi) = bouts n ci

body :: Re (Bn t) -> Re t
body (((n, bi) :\\ t) :^ ai) = t :^ bins ai n bi

data Sp x = S0 | SZ (PR (Sp x) x) deriving Show

unSp :: Re (Sp x) -> Bwd (Re x)
unSp (S0 :^ _) = B0
unSp (SZ (xz, x) :^ ci) = unSp (xz ^<< ci) :\ (x ^<< ci)

(-\) :: Re (Sp x) -> Re x -> Re (Sp x)
xz -\ x = fmap SZ (pR xz x)

sp :: Bwd (Re x) -> Re (Sp x)
sp B0        = kR S0
sp (xz :\ x) = sp xz -\ x

pll :: OPE -> OPE -> (OPE, OPE)
pll (-1) bi = (bi, oi)
pll ai (-1) = (oi, ai)
pll 0    bi = (oe, oe)
pll ai    0 = (oe, oe)
pll ai       bi = case (bout ai, bout bi) of
  ((ai, True),   (bi, True))    -> (os *** os) (pll ai bi)
  ((ai, True),   (bi, False))   -> (o' *** id) (pll ai bi)
  ((ai, False),  (bi, True))    -> (id *** o') (pll ai bi)
  ((ai, False),  (bi, False))   -> pll ai bi
