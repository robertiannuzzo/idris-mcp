module Data.Container.Descriptions.List

import Data.Container.Definition
import Data.Container.Morphism
import Data.Container.Category
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.ForallSeq.Definition
import Data.Container.ForallSeq.Bifunctor
import Data.Container.List.Desc
import Data.Container.List.Functor

import Data.Category.Bifunctor
import Data.Category.Endofunctor
import Data.Category.Monad
import Data.Category.NaturalTransformation

import Data.Fin
import Data.List
import Data.List.Monad
import Data.Sigma
import public Data.List.Quantifiers
import Data.Iso

import Proofs

%default total
public export
concat : TyList a -> TyList a -> TyList a
concat (MkEx Z dd) y = y
concat (MkEx (S n) dd) y = assert_total $ Cons (dd FZ) (concat (MkEx n (dd . FS)) y)

public export
singleton : a -> TyList a
singleton x = Cons x Nil

public export
pure : a =%> Forall a
pure =
    singleton <! bwd
    where
      bwd : (x : a.req) -> (Forall a).res (singleton x) -> a.res x
      -- bwd x f = f FZ

public export
listAppend : List a -> List a -> List a
listAppend [] ys = ys
listAppend (x :: xs) ys = x :: xs ++ ys
public export
map1 : (a -> b) -> (a, x) -> (b, x)
map1 f y = (f (fst y), snd y)

public export
splitLocal : (xs : List a) -> All p (xs ++ ys) -> (All p xs, All p ys)
splitLocal [] pxs = ([], pxs)
splitLocal (_ :: xs) (px :: pxs) = map1 (px ::) (splitLocal xs pxs)

public export
allHead : All f (x :: xs) -> f x
allHead (y :: z) = y

namespace All
  public export
  pure : x =%> All.List x
  pure = (:: []) <! (\x, y => allHead y)

  public export
  joinBwd : (val : List (List (x .req))) -> All (x .res) (joinList val) -> All (All (x .res)) val
  joinBwd [] x = []
  joinBwd (y :: xs) arg = let k : (All x.res y, All x.res (joinList xs))
                              k = splitLocal y arg
                           in fst k :: joinBwd xs (snd k)

  public export
  join : All.List (All.List x) =%> All.List x
  join = joinList <! joinBwd

%unbound_implicits off
public export
listMapAppend : forall a, b . {0 f : a -> b} -> {xs, ys : List a} -> map f (xs ++ ys) === map f xs ++ map f ys
listMapAppend {xs = []} = Refl
listMapAppend {xs = (x :: xs)} = cong (f x ::) (listMapAppend {xs})

public export
mapProp : forall a, b. {f : a -> b} -> {0 p : b -> Type} -> {0 q : a -> Type} ->
          (fn : (x : a) -> p (f x) -> q x) ->
          (v : List a) ->
          All p (map f v) ->
          All q v
mapProp fn [] x = []
mapProp fn (x :: xs) (y :: ys) = fn x y :: mapProp fn xs ys

public export
AllCFunctor : {0 x, y : Container} -> x =%> y -> All.List x =%> All.List y
AllCFunctor mor =
    (map mor.fwd) <!
    (mapProp {f = mor.fwd, p = y.res, q = x.res} mor.bwd)

public export 0
listMapId : forall a. (x : List a) -> map Prelude.id x = Prelude.id x
listMapId [] = Refl
listMapId (x :: xs) = cong (x ::) (listMapId xs)

public export 0
mapPropId : forall a. {p : a -> Type} -> (x : List a) -> (y : All p x) ->
            mapProp {f = Prelude.id} (\_ => Prelude.id) x (rewrite__impl (All p) (listMapId x) y) === y
mapPropId [] [] = Refl
mapPropId (x :: xs) (y :: ys) = cong (y ::) (mapPropId xs ys)

public export
allCompFwd : forall a, b, c. (h : b -> c) -> (g : a -> b) -> (xs : List a) -> map (h . g) xs = (map h (map g xs))
allCompFwd h g [] = Refl
allCompFwd h g (x :: xs) = cong (h (g x) ::) (allCompFwd h g xs)

%unbound_implicits off
allCompBwd : {0 a, b, c : Type} ->
    {gf : a -> b} ->
    {hg : b -> c} ->
    {p : b -> Type} ->
    {q : a -> Type} ->
    {r : c -> Type} ->
    {g : (v : a) -> p (gf v) -> q v} ->
    {h : (x : b) -> r (hg x) -> p x} ->
    (x : List a) ->
    (y : All r (map (hg . gf) x)) ->
    let
      0 ll : All p (map gf x)
      ll = mapProp {f = hg, p = r, q = p} h (map gf x) (rewrite__impl (All r) (sym $ allCompFwd hg gf x) y)
      0 tt : All q x
      tt = mapProp {f = gf, p, q} g x ll
      rr : All q x
      rr = mapProp (\z, w => g z (h (gf z) w)) x y
    in rr === tt
allCompBwd [] y = Refl
allCompBwd (x :: xs) (y :: ys) = cong (g x (h (gf x) y) ::) (allCompBwd xs ys)


%unbound_implicits on
public export
AllCFunctorFunc : Endo Cont
AllCFunctorFunc = MkFunctor
  All.List
  (\_, _ => AllCFunctor)
  (\c => cong2Dep'
    (<!)
    (funExt listMapId)
    (funExtDep $ \x => funExt $ \y => mapPropId x (rewrite__impl (All c.res) (sym $ listMapId x) y)))
  (\a, b, c, g, h => cong2Dep' (<!)
      (funExt $ \x => allCompFwd h.fwd g.fwd x)
      (funExtDep $ \x => funExt $ \y =>
        allCompBwd {hg = h.fwd, p = b.res, g = g.bwd, h = h.bwd} x y))
        {-


listAllEqToEq : {0 a : Type} -> {0 p : a -> Type} -> {0 q : a -> Type} ->
                {prf : p ≡ q} ->
                {ls : List a} -> {xs : All p ls} -> {ys : All q ls} ->
                ForallEq {ls, prf} xs ys -> ys ≡ replace {p = \vx => All vx ls} prf xs
listAllEqToEq {ls = [], prf = Refl} AllEmpty = Refl
listAllEqToEq {ls = y :: zs} (AllCons {prf = Refl, prf2 = Refl} z z w) = cong (z ::) (listAllEqToEq w)

%unbound_implicits off
joinAllBwd : {0 a : Container} ->
    (v : List (List (List a.request))) ->
    (y : All a.response (joinList (joinList v))) -> let
      x1 : List (List a.request)
      x1 = map joinList v
      0 sq := app (ListIsMonad .square a.request) v
      0 x2 : All (All (a .response)) (mapImpl joinList v)
      x2 = (joinBwd {x = a} x1 (replace {p = All a.response} (sym sq) y))
      0 x3, yn : All (\arg => All (All (a .response)) arg) v
      x3 = mapProp {a = List (List a.req), b = List a.req, p = All a.res, f = joinList
                   , q = All (All a.res)}
                   (joinBwd {x = a}) v x2
      yn = joinBwd {x = All.List a} v (joinBwd (joinList v) y)
    in x3 ≡ yn
joinAllBwd [] y = Refl
joinAllBwd (x :: xs) y = ?joinAllBwd_rhs_1

    {-
public export
data ForallAllEq : {0 a : Type} ->
                 {0 p : a -> Type} ->
                 {0 q : a -> Type} ->
                 (l1 : List (List a)) ->
                 All (All.All p) l1 ->
                 All (All.All q) l1 -> Type where
                   -- listMap (m .fwd) (joinList v) and joinList (left .fwd v)
  AllAllEmpty : {0 a : Type} ->
             {0 p : a -> Type} ->
             {0 q : a -> Type} -> ForallAllEq {a, p, q} [] [] []
  -- AllAllCons : {0 a : Type} ->
  --           {0 p : a -> Type} ->
  --           {0 q : a -> Type} ->
  --           {l1 : List (List a)} ->
  --           {p1 : All (All p) l1} ->
  --           {p2 : All (All q) l1} ->
  --           (v : List a) ->
  --           (w1 : All p v) ->
  --           (w2 : All q v) ->
  --           (ford : ForallEq w1 w2) ->
  --           ForallAllEq {a, p, q} l1 p1 p2 ->
  --           ForallAllEq {a, p, q} (v :: l1) (w1 :: p1) (w2 :: p2)

-- public export
-- listEqToEq : {0 a : Type} -> {0 p : a -> Type} -> {l1, l2 : List a} -> {a1 : All p l1} -> {a2 : All p l2} ->
--              ForallEq l1 l2 a1 a2 -> l1 === l2
-- listEqToEq AllEmpty = Refl
-- listEqToEq (AllCons v w w Refl x) = cong (v ::) (listEqToEq x)
--
-- export
-- listEqToEq' : {0 a : Type} -> {0 p : a -> Type} -> {l1, l2 : List a} -> {a1 : All p l1} -> {a2 : All p l2} ->
--              (prf : ForallEq l1 l2 a1 a2) -> a1 === replace {p = All p} (sym $ listEqToEq prf) a2
-- listEqToEq' AllEmpty = Refl
-- listEqToEq' (AllCons v w w Refl x) = ?Hue
-- listEqToEq' (AllConcat w x) = ?Hue2
-- export
-- listEqToEq : {0 a : Type} -> {0 p : a -> Type} -> {l1, l2 : List a} -> {a1 : All p l1} -> {a2 : All p l2} ->
--              ForallEq l1 l2 a1 a2 -> l1 === l2
-- listEqToEq AllEmpty = Refl
-- listEqToEq (AllCons v w1 w1 Refl x) = cong (v ::) (listEqToEq x)
--
-- export
-- listEqToEq' : {0 a : Type} -> {0 p : a -> Type} -> {l1, l2 : List a} -> {a1 : All p l1} -> {a2 : All p l2} ->
--              (prf : ForallEq l1 l2 a1 a2) -> a1 === rewrite__impl (All p) (listEqToEq prf) a2
-- listEqToEq' AllEmpty = Refl
-- listEqToEq' (AllCons v w1 w1 Refl x) with (listEqToEq x)
--   _ | Refl = cong (w1 ::) (listEqToEq' x)
--
-- data ListFlatMapTwice : {a, b : Type} -> {ls : List (List a)} -> {p : b -> Type} ->
--     {f : a -> b} -> All p (listMap f (joinList ls)) -> All p (joinList (listMap (listMap f) ls)) -> Type where
--       FNil : ListFlatMapTwice {ls = []} [] []
--       FCons :


-- A simpler way to defined the bifunctor is to apply the list continer to the `▶` bifunctor


----------------------------------------------------------------------------------
-- Any Lists
----------------------------------------------------------------------------------


AnyToList : Any.List x =%> Forany x
AnyToList =
    tyListIso.from <! bwd
    where
      bwd : (v : List (x.req)) ->
            Σ (Fin ((listToTyList v).ex1)) (\y => x.res ((listToTyList v).ex2 y)) ->
            Any (x.res) v
      bwd [] x = absurd x.π1
      bwd (x :: xs) (FZ ## p2) = Here p2
      bwd (x :: xs) (FS p1 ## p2) = There (bwd xs (p1 ## p2))

ListToAny : Forany x =%> Any.List x
ListToAny =
    tyListIso.to <! bwd
    where
      bwd : (v : TyList x.req) ->
            Any (x .res) (tyListToList v) ->
            Σ (Fin (v.ex1)) (\y => x .res (v.ex2 y))
      bwd (MkEx 0 v2) x = absurd x
      bwd (MkEx (S k) v2) (Here x) = FZ ## x
      bwd (MkEx (S k) v2) (There x) = let rec = bwd (MkEx k (v2 . FS)) x in FS rec.π1 ## rec.π2

public export
ForanyFunctor : Endo Cont
ForanyFunctor = applyBifunctor {a = Cont, b = Cont} ListCont ComposeBifunctor

public export
joinListMap : (f : a -> b) -> (v : List (List a)) -> (map f (joinList v)) === (joinList (map (map f) v))
joinListMap f [] = Refl
joinListMap f (x :: xs) = trans (listMapAppend) (cong (map f x ++) (joinListMap f xs))


public export
mapPropAppend : {0 a, b : Type} ->
                {0 f : a -> b} -> {0 p : b -> Type} -> {0 q : a -> Type} ->
                (xs : List a) -> (vs : All p (map f xs)) ->
                (ys : List a) -> (ws : All p (map f ys)) ->
                (gn : (x : a) -> p (f x) -> q x) ->
                mapProp gn (xs ++ ys) (rewrite__impl (All p) ((List.listMapAppend {f, xs, ys})) (vs ++ ws)) ===
                  mapProp gn xs vs ++ mapProp gn ys ws
mapPropAppend [] [] ys ws gn = Refl
mapPropAppend (x :: xs) (v :: vs) ys ws gn = cong (gn x v :: ) (mapPropAppend xs vs ys ws gn)

public export
fromList : ((x : a) -> p x) -> (xs : List a) -> All p xs
fromList _ [] = []
fromList e (x :: xs) = e x :: fromList e xs
public export
ForallIdris : Container -> Container
ForallIdris c = (!>) (List c.req) (All c.res)

{-
allToIdris : Forall x =%> ForallIdris x
allToIdris =
    tyListIso.to <!
    bwd
    where
      bwd : (v : Σ Nat (\y => Fin y -> x .req)) -> All x.res (tyListToList v) -> (val : Fin (v.π1)) -> x.res (v.π2 val)
      bwd (0 ## p2) _ val impossible
      bwd ((S k) ## p2) (x :: xs) FZ = x
      bwd ((S k) ## p2) (x :: xs) (FS v) = bwd (k ## p2 . FS) xs v

toForall : ForallIdris x =%> Forall x
toForall =
    tyListIso.from <!
    bwd
    where
      bwd : (v : List x.req) -> ((val : Fin ((listToTyList v).π1)) -> x .res ((listToTyList v).π2 val)) -> All x.res v
      bwd [] f = []
      bwd (y :: (xs)) f = f FZ :: bwd xs (\x => f (FS x))

public export
join : Forall (Forall x) =%> Forall x
join = let
      pre2 : Forall (ForallIdris x) =%> ForallIdris (ForallIdris x)
      pre2 = fromForall {x = ForallIdris x}

      pre1 : Forall  (Forall x) =%> Forall (ForallIdris x)
      pre1 = univFunctor {a = ListCont} fromForall

    in pre1 |> pre2 |> join' |> toForall

public export
ForallIdrisFunctor : {x, y : Container} -> x =%> y -> ForallIdris x =%> ForallIdris y
ForallIdrisFunctor mor =
    (map mor.fwd) <! bwd
    where
      bwd : (v : List (x .req)) -> All (y .res) (mapImpl (mor.fwd) v) -> All (x .res) v
      bwd [] x = []
      bwd (x :: xs) (y :: ys) = mor.bwd x y :: bwd xs ys
