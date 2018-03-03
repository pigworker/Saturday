{-# LANGUAGE OverloadedStrings #-}

module Tm where

import Control.Arrow ((***))
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
  = X (PR () (Sp (Bn TC)))
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

rtS :: Re () -> Re (Sp (Bn TC)) -> Bwd (A, Ki) -> [Ki] -> [RC] -> Maybe (Re TE)
rtS x tz g [] ts = rtZ (fmap X (pR x tz)) g ts
rtS x tz g (k : ks) [] = Nothing
rtS x tz g (Ki k : ks) (t : ts) = do
  t <- rtB g 0 k t
  rtS x (tz -\ t) g ks ts

rtB :: Bwd (A, Ki) -> Int -> [Ki] -> RC -> Maybe (Re (Bn TC))
rtB g n [] t = (n \\) <$> rtC g t
rtB g n (k : ks) (Ld x t) = rtB (g :\ (x, k)) (n + 1) ks t
rtB _ _ _ _ = Nothing

rtZ :: Re TE -> Bwd (A, Ki) -> [RC] -> Maybe (Re TE)
rtZ e g [] = return e
rtZ e g (t : ts) = do
  t <- rtC g t
  rtZ (fmap Z (pR e t)) g ts

