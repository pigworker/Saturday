{-# LANGUAGE OverloadedStrings, FlexibleInstances, TypeSynonymInstances #-}

module Tm where

import Control.Arrow ((***))
import Data.Bits
import R
import B

data TC
  = A A
  | V
  | P (PR TC TC)
  | I TC
  | L (Bn TC)     -- never nullary
  | E TE
  deriving Show

data TE
  = X (PR () (Sp (Bn TE)))
  | Z (PR TE TC)
  | T (PR TC TC)
  deriving Show

data Ki = Ki [Ki]

rtC :: Bwd (A, Ki) -> RC -> Maybe (Re TC)
rtC _ (At a)    = return (kR (A a))
rtC _ Vd        = return (kR V)
rtC g (s :. t)  = fmap P <$> (pR <$> rtC g s <*>rtC g t)
rtC g (In t)    = fmap I <$> rtC g t
rtC g (Em e)    = fmap E <$> rtE g e []
rtC g t         = fmap L <$> ((n \\) <$> rtC g' t') where
  (n, g', t') = lu 0 g t
  lu n g (Ld x t) = lu (n + 1) (g :\ (x, Ki [])) t
  lu n g t = (n, g, t)

rtX :: Bwd (A, Ki) -> A -> Int -> Maybe (Int, Ki)
rtX B0 _ _ = Nothing
rtX (g :\ (y, k)) x i
  | x == y     = if i == 0 then Just (0, k) else rt' <$> rtX g x (i - 1)
  | otherwise  = rt' <$> rtX g x i
  where rt' = succ *** id
  
rtE :: Bwd (A, Ki) -> RE -> [RC] -> Maybe (Re TE)
rtE g (e :$ t) ts = rtE g e (t : ts)
rtE g (s :< t) ts = do
  e <- fmap T <$> (pR <$> rtC g s <*> rtC g t)
  rtZ e g ts
rtE g (x :# i) ts = do
  (j, Ki ks) <- rtX g x i
  rtS (xR j) (kR S0) g ks ts

rtS :: Re () -> Re (Sp (Bn TE)) -> Bwd (A, Ki) -> [Ki] -> [RC] -> Maybe (Re TE)
rtS x tz g [] ts = rtZ (fmap X (pR x tz)) g ts
rtS x tz g (Ki k : ks) (t : ts) = do
  t <- rtB g 0 k t
  rtS x (tz -\ t) g ks ts
rtS _ _ _ _ _ = Nothing

rtB :: Bwd (A, Ki) -> Int -> [Ki] -> RC -> Maybe (Re (Bn TE))
rtB g n [] (Em e) = (n \\) <$> rtE g e []
rtB g n (k : ks) (Ld x t) = rtB (g :\ (x, k)) (n + 1) ks t
rtB _ _ _ _ = Nothing

rtZ :: Re TE -> Bwd (A, Ki) -> [RC] -> Maybe (Re TE)
rtZ e g [] = return e
rtZ e g (t : ts) = do
  t <- rtC g t
  rtZ (fmap Z (pR e t)) g ts



upsilon :: Re TE -> Re TC
upsilon (T (t, _) :^ bi) = t ^<< bi
upsilon e = fmap E e

data HSub = HSub {leave :: OPE, subst :: OPE, images :: Bwd (Re (Bn TE))}
  deriving Show

(<%) :: OPE -> HSub -> HSub
bi <% HSub th ps sz = HSub (th0 << th) bi0 (ps0 <?? sz) where
  (bi0, ps0) = pll bi ps
  (_, th0)   = pll bi (complement ps)

(%+) :: HSub -> (Int, OPE) -> HSub
HSub th ps sz %+ (n, bi) = HSub (bins th n bi) (shiftL ps n) sz

class HSUB t where
  hs, hsWk :: HSub -> t -> Re t
  hs (HSub bi _ B0) t = t :^ bi
  hs sb t = hsWk sb t

instance HSUB t => HSUB (Re t) where
  hsWk sb (t :^ bi) = hs (bi <% sb) t :^ oi

instance (HSUB s, HSUB t) => HSUB (PR s t) where
  hs = hsWk
  hsWk sb (s :^ ai, t :^ bi) = pR (hs (ai <% sb) s) (hs (bi <% sb) t)

instance HSUB TC where
  hsWk sb (I t)  = fmap I (hs sb t)
  hsWk sb (P st) = fmap P (hs sb st)
  hsWk sb (L t)  = fmap L (hs sb t)
  hsWk sb (E e)  = upsilon (hs sb e)

instance HSUB TE where
  hsWk sb (X (() :^ x, sp :^ ai)) = case x <% sb of
    HSub y _ B0  -> fmap X (pR (() :^ y) sp')
    HSub _ _ (_ :\ (((n, bi) :\\ t) :^ th)) ->
      hs (HSub th (bins oe (bi <? n) oi) (bi <?? unSp sp')) t
   where
    sp' = hs (ai <% sb) sp
  hsWk sb (Z et) = fmap Z (hs sb et)
  hsWk sb (T tT) = fmap T (hs sb tT)

instance HSUB t => HSUB (Sp t) where
  hsWk sb (SZ p) = fmap SZ (hs sb p)

instance HSUB t => HSUB (Bn t) where
  hsWk sb (p@(n, _) :\\ e) = n \\ hs (sb %+ p) e
