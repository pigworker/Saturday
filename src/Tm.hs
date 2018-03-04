{-# LANGUAGE OverloadedStrings, FlexibleInstances, TypeSynonymInstances,
    PatternGuards #-}

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
  | L (Bn TC)     -- never nullary, never nested
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
    HSub _ _ (_ :\ pv) -> stan pv sp'
   where
    sp' = hs (ai <% sb) sp
  hsWk sb (Z et) = fmap Z (hs sb et)
  hsWk sb (T tT) = fmap T (hs sb tT)

stan :: HSUB t => Re (Bn t) -> Re (Sp (Bn TE)) -> Re t
stan (((n, bi) :\\ t) :^ th) sp =
  hs (HSub th (bins oe (bi <? n) oi) (bi <?? unSp sp)) t

instance HSUB t => HSUB (Sp t) where
  hsWk sb (SZ p) = fmap SZ (hs sb p)

instance HSUB t => HSUB (Bn t) where
  hsWk sb (p@(n, _) :\\ e) = n \\ hs (sb %+ p) e


ld :: Bn TC -> TC
ld ((0, _) :\\ t) = t
ld ((n, ai) :\\ L ((m, bi) :\\ t)) = L ((n + m, bins ai m bi) :\\ t)
ld b = L b

isL1 :: Re TC -> Maybe (Re (Bn TC))
isL1 (L ((0, _) :\\ t) :^ bi) = isL1 (t :^ bi)
isL1 (L b@((1, _) :\\ _) :^ bi) = Just (b :^ bi)
isL1 (L ((n, ai) :\\ t) :^ bi) =
  Just (((1, ci) :\\ ld (((n - 1), di) :\\ t)) :^ bi) where
  (ci, di) = bouts (n - 1) ai

isL1 _ = Nothing

type Cx = Bwd (Re (Bn TC))

data Share x = Share {changed :: !Bool, value :: x}

instance Applicative Share where
  pure x = Share False x
  Share cf f <*> Share cs s = Share (cf || cs) (f s)

instance Functor Share where
  fmap f (Share c x) = Share c (f x)

share :: t -> Share t -> Share t
share t (Share b t') = Share b (if b then t' else t)

new :: t -> Share t
new = Share True

rnfC :: Cx -> Re TC -> Share (Re TC)
rnfC g z@(t :^ bi) = share z $ case t of
  I t  -> fmap I <$> rnfC g (t :^ bi)
  P st -> case prjR (st :^ bi) of
    (s, t) -> fmap P <$> (pR <$> rnfC g s <*> rnfC g t)
  E e  -> upsilon <$> fst (rnfE g (e :^ bi))
  _ -> pure z

rnfE :: Cx -> Re TE -> (Share (Re TE), Re TC)
rnfE g z@(e :^ bi) = (share z *** id) $ case e of
  T tty -> case prjR (tty :^ bi) of
    (t, ty) -> let ty' = rnfC g ty
               in  (fmap T <$> (pR <$> rnfC g t <*> ty'), value ty')
  X vs -> case prjR (vs :^ bi) of
    (() :^ x, sz) -> case x <?? g of
      B0 :\ pty ->
        let ty = value (rnfC g (stan pty sz))
        in  (pure z, ty)
  Z es -> case prjR (es :^ bi) of
    (e, s) -> elim g (rnfE g e) s

radR :: Re TC -> Re TC -> Re TE
radR t tT = fmap T (pR t tT)

elim :: Cx -> (Share (Re TE), Re TC) -> Re TC -> (Share (Re TE), Re TC)
elim g (e, ty) s = flip (,) ty' $ case isCan ty of
    Just ("Pi", [sS, tT])
      | Just (f, _) <- isRad (value e), Just bt <- isL1 f ->
         new (radR (stan bt (tTspine s sS)) ty')
    _ -> fmap Z <$> (pR <$> e <*> pure s)
  where
    ty' = elimTy g (value e, ty) s

elimTy :: Cx -> (Re TE, Re TC) -> Re TC -> Re TC
elimTy g (e, ty) s = case isCan ty of
  Just ("Pi", [sS, tT]) | Just tTb <- isL1 tT ->
    stan tTb (tTspine s sS)

tTspine :: Re TC -> Re TC -> Re (Sp (Bn TE))
tTspine s sS = fmap SZ (pR (kR S0) (0 \\ radR s sS))

isRad :: Re TE -> Maybe (Re TC, Re TC)
isRad (T tT :^ bi) = pure (prjR (tT :^ bi))
isRad _ = Nothing

isList :: Re TC -> Maybe [Re TC]
isList (V :^ _) = pure []
isList (P st :^ bi) = case prjR (st :^ bi) of
  (s, t) -> (s :) <$> isList t

isCan :: Re TC -> Maybe (A, [Re TC])
isCan (I (P ct) :^ bi) = case prjR (ct :^ bi) of
  (A x :^ _, t) -> (,) x <$> isList t
  _ -> Nothing
isCan _ = Nothing