{-# LANGUAGE OverloadedStrings, FlexibleInstances, TypeSynonymInstances,
    PatternGuards #-}

module Tm where

import Control.Arrow ((***))
import Control.Monad
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

rnfC :: Cx -> Re TC -> Re TC
rnfC g z@(t :^ bi) = case t of
  I t  -> fmap I (rnfC g (t :^ bi))
  P st -> case prjR (st :^ bi) of
    (s, t) -> fmap P (pR (rnfC g s) (rnfC g t))
  E e  -> upsilon (fst (rnfE g (e :^ bi)))
  _ -> z

rnfE :: Cx -> Re TE -> (Re TE, Re TC)
rnfE g z@(e :^ bi) = case e of
  T tty -> case prjR (tty :^ bi) of
    (t, ty) -> let ty' = rnfC g ty
               in  (radR (rnfC g t) ty', ty')
  X vs -> case prjR (vs :^ bi) of
    (() :^ x, sz) -> case x <?? g of
      B0 :\ pty -> (z, rnfC g (stan pty sz))
  Z es -> case prjR (es :^ bi) of
    (e, s) -> elim g (rnfE g e) s

radR :: Re TC -> Re TC -> Re TE
radR t tT = fmap T (pR t tT)

elim :: Cx -> (Re TE, Re TC) -> Re TC -> (Re TE, Re TC)
elim g z@(e, ty) s = flip (,) ty' $ case isCan ty of
    Just ("Pi", [sS, tT]) | Just (f, _) <- isRad e, Just bt <- isL1 f ->
      radR (stan bt (tTspine s sS)) ty'
    _ -> fmap Z (pR e s)
  where
    ty' = elimTy g z s

elimTy :: Cx -> (Re TE, Re TC) -> Re TC -> Re TC
elimTy g (e, ty) s = case isCan ty of
  Just ("Pi", [sS, tT]) | Just bT <- isL1 tT ->
    stan bT (tTspine s sS)

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

sortGt :: Re TC -> Re TC -> Maybe ()
sortGt _ _ = Just ()  -- bullshit, for now

sortGe :: Re TC -> Re TC -> Maybe ()
sortGe _ _ = Just ()  -- bullshit, for now

canQ :: Cx -> Re TC -> Re TC -> Maybe ()
canQ g i j = do
  (i, ss) <- isCan i
  (j, ts) <- isCan j
  guard (i == j)
  go ss ts
 where
  go [] [] = return ()
  go (s : ss) (t : ts) = do
    canQ g (rnfC g s) (rnfC g t)
    go ss ts
  go _ _ = Nothing

pushCx :: Cx -> Re TC -> (Cx -> Re TE -> t) -> t
pushCx g sS k =
  k (fmap (^<< o' oi) (g :\ (0 \\ sS)))
    (fmap X (pR (xR 0) (kR S0)))

isE :: Re TC -> Maybe (Re TE)
isE (E e :^ bi) = Just (e :^ bi)
isE _ = Nothing

data Can
  = A :/ [Can]
  | Y (Re TC)

can :: Can -> Re TC
can (h :/ cs)  = fmap (I . P) (pR (kR (A h)) (cans cs)) where
  cans []        = kR V
  cans (c : cs)  = fmap P (pR (can c) (cans cs))
can (Y t)      = t

topSort :: Re TC
topSort = can ("Type" :/ ["Type" :/ []])

wk :: Re t -> Re t
wk (t :^ bi) = t :^ o' bi

chk :: Cx        -- context
    -> Re TC     -- type to check, already in rnf
    -> Re TC     -- candidate inhabitant
    -> Maybe ()  -- well, did ya?
chk g ty tm@(t :^ bi) = case (isCan ty, isCan tm) of
  (Just ("Type", [j]), Just ("Type", [i])) -> sortGt (rnfC g j) (rnfC g i)
  (Just ("Type", _), Just ("Pi", [sS, tT])) -> do
    bT <- isL1 tT
    chk g ty sS
    pushCx g sS $ \ g x -> chk g (wk ty) (body bT)
  (Just ("Pi", [sS, tT]), _) | Just bt <- isL1 tm -> do
    bT <- isL1 tT
    pushCx g sS $ \ g x -> chk g (rnfC g (body bT)) (body bt)
  _ | Just e <- isE tm -> do
    sTy <- syn g e
    subtype g sTy ty
  _ -> Nothing

syn :: Cx              -- context
    -> Re TE           -- elimination for which to synthesize type
    -> Maybe (Re TC)   -- synthesized type in rnf
syn g e | Just (tm, ty) <- isRad e = do
  chk g topSort ty
  chk g ty tm
  return (rnfC g ty)
syn g (X xsz :^ bi) = do
  let (() :^ x, sz) = prjR (xsz :^ bi)
  let B0 :\ pty = x <?? g
  -- really ought to check that the sz are ok
  -- but that probably needs more info than I've currently stashed
  -- in the context;
  -- it's fine for obj vars where sz is empty anyway
  -- but not for metas
  return (rnfC g (stan pty sz))
syn g (Z es :^ bi) = do
  let (e, s) = prjR (es :^ bi)
  ty <- syn g e
  case isCan ty of
    Just ("Pi", [sS, tT]) -> do
      chk g (rnfC g sS) s
      bT <- isL1 tT
      return (rnfC g (stan bT (tTspine s sS)))
    _ -> Nothing
syn g e = Nothing

subtype :: Cx        -- context
        -> Re TC     -- candidate subtype in rnf
        -> Re TC     -- candidate supertype in rnf
        -> Maybe ()  -- well, did ya?
subtype g s t = case (isCan s, isCan t) of
  (Just ("Type", [i]),     Just ("Type", [j])) ->
    sortGe (rnfC g j) (rnfC g i)
  (Just ("Pi", [sS, sT]),  Just ("Pi", [tS, tT]))  -> do
    subtype g (rnfC g tS) (rnfC g sS)
    bsT <- isL1 sT
    btT <- isL1 tT
    pushCx g tS $ \ g x -> subtype g (rnfC g (body bsT)) (rnfC g (body btT))
  _ -> do
    sE <- isE s
    tE <- isE t
    _ <- qE g sE tE
    return ()

qE :: Cx             -- context
   -> Re TE          -- e the first in rnf
   -> Re TE          -- e the second in rnf
   -> Maybe (Re TC)  -- are they equal with a synthesized type in rnf
qE g e0 e1 | Just (tm, ty) <- isRad e0, Just e <- isE tm = qE g e e1
qE g e0 e1 | Just (tm, ty) <- isRad e1, Just e <- isE tm = qE g e0 e
qE g e@(X xsz :^ ai) (X ytz :^ bi) = case (prjR (xsz :^ ai), prjR (ytz :^ bi)) of
  ((() :^ x, sz :^ ai), (() :^ y, tz :^ bi)) -> do
    guard (qOPE (blen g) x y)
    -- compare spines
    syn g e
qE g (Z es0 :^ ai) (Z es1 :^ bi) = case (prjR (es0 :^ ai), prjR (es1 :^ bi)) of
  ((e0, s0), (e1, s1)) -> do
    ty <- qE g e0 e1
    case isCan ty of
      Just ("Pi", [sS, tT]) -> do
        let sS' = rnfC g sS
        let s0' = rnfC g s0
        qC g sS' s0' (rnfC g s1)
        bT <- isL1 tT
        return (rnfC g (stan bT (tTspine s0' sS')))
      _ -> Nothing
qE _ _ _ = Nothing

qC :: Cx           -- context
   -> Re TC        -- type in rnf
   -> Re TC        -- t the first in rnf
   -> Re TC        -- t the second in rnf
   -> Maybe ()     -- well, were they?
qC g ty t0 t1 = case (isCan ty, isCan t0, isCan t1) of
  (Just ("Type", _), Just ("Type", [i]), Just ("Type", [j])) ->
    canQ g (rnfC g i) (rnfC g j)
  (Just ("Type", _), Just ("Pi", [sS, sT]), Just ("Pi", [tS, tT])) -> do
    qC g ty (rnfC g sS) (rnfC g tS)
    bsT <- isL1 sT
    btT <- isL1 tT
    pushCx g sS $ \ g x -> qC g (wk ty) (rnfC g (body bsT)) (rnfC g (body btT))
  (Just ty@("Pi", [sS, tT]), _, _) -> do
    bT <- isL1 tT
    b0 <- isL1 (etaPi t0)
    b1 <- isL1 (etaPi t1)
    pushCx g sS $ \ g x ->
      qC g (rnfC g (body bT)) (rnfC g (body b0)) (rnfC g (body b1))
  _ -> do
    e0 <- isE t0
    e1 <- isE t1
    qE g e0 e1
    return ()


etaPi :: Re TC -> Re TC
etaPi (E e :^ bi) =
  fmap L (1 \\ fmap (E . Z) (pR (e :^ o' bi)
    (fmap (E . X) (pR (xR 0) (kR S0)))))
etaPi t = t