module Data.List.Monad

import public Data.List
import Data.Product
import Data.Iso.Generic

import Data.Category
import Data.Category.Functor
import Data.Category.Endofunctor
import Data.Category.Monad
import Data.Category.Monad.Cartesian
import Data.Category.NaturalTransformation

import Proofs.List

listMapId : (xs : List a) -> map Prelude.id xs === xs
listMapId [] = Refl
listMapId (x :: xs) = cong (x ::) (listMapId xs)

listMapCompose : {0 a, b, c :  Type} ->
                 (f : a -> b) -> (g : b -> c) ->
                 (xs : List a) -> map g (map f xs) === map (g . f) xs
listMapCompose f g [] = Refl
listMapCompose f g (x :: xs) = cong (g (f x) ::) (listMapCompose f g xs)

public export
ListIsFunctor : Endo Set
ListIsFunctor = MkFunctor
  List
  (\_, _ => map)
  (\_ => funExt listMapId)
  (\a, b, c, f, g => sym $ funExt $ listMapCompose f g)

public export
joinList : List (List a) -> List a
joinList [] = []
joinList (x :: xs) = x ++ joinList xs

joinJoinMap : (f : a -> b) -> (xs : List (List a)) ->
              map f (joinList xs) === joinList (map (map f) xs)
joinJoinMap f [] = Refl
joinJoinMap f (x :: xs) = trans
  (mapAppend f x (joinList xs))
  (cong (mapImpl f x ++) (joinJoinMap f xs))

joinListAppend : (xs, ys : List (List a)) -> joinList (xs ++ ys) ≡ joinList xs ++ joinList ys
joinListAppend [] ys = Refl
joinListAppend (x :: xs) ys =
  let rec = joinListAppend xs ys
      app = appendAssociative x (joinList xs) (joinList ys)
  in trans (cong (x ++) rec) (app)

joinListSquare : (xs : List (List (List a))) ->
                 joinList (joinList {a = List a} xs) ≡ joinList (map (joinList {a}) xs)
joinListSquare [] = Refl
joinListSquare (x :: xs) =
  let rec = joinListSquare xs
      step1 = joinListAppend x (joinList xs)
  in trans step1 (cong (joinList x ++) rec)

joinSingle  : (xs : List a) -> joinList (mapImpl List.singleton xs) ≡ xs
joinSingle [] = Refl
joinSingle (x :: xs) = cong (x ::) (joinSingle xs)

public export
ListIsMonad : Monad Set ListIsFunctor
ListIsMonad = MkMonad
  (MkNT (\_ => singleton)
     (\_, _, f => Refl))
  (MkNT (\_ => joinList)
      (\_, _, f => funExt (joinJoinMap f)))
  (\x => funExt (\xs => sym (joinListSquare xs)))
  (\x => funExt appendNilRightNeutral)
  (\x => funExt joinSingle)

getHead :
   (xs : List a) -> {y : b} -> {f : a -> b} ->
   (prf : map f xs === [y]) ->
   a
getHead (x :: xs) prf = x

getHeadElem : {0 a, b : Type} -> {y : b} -> {f : a -> b} ->
              (xs : List a) -> {prf : map f xs === [y]} ->
              [getHead {y, f} xs prf] === xs
getHeadElem (x :: []) = Refl

mapSingletonF :
  {0 a, b : Type} -> {y : b} -> {f : a -> b} ->
  (xs : List a) ->
  (qq : mapImpl f xs = [y]) ->
  -- (ww : [getHead (xx w) prf] = xx w) ->
  f (getHead {y, f} xs qq) = y
mapSingletonF (x :: []) Refl = Refl

splitCons : {a, b : x} -> {as, bs : List x} ->
            (a :: as) = (b :: bs) -> (a = b) * (as = bs)

splitMapJoin : {0 x, y : Type} ->
   (z : List y) ->
   (xs : List (List y)) ->
   (f : x -> y) ->
   (vx : List x) ->
   (pp : mapImpl f vx = z ++ joinList xs) ->
   Σ (vxPrefix : List x) | Σ (vxPostfix : List x) |
    (map f vxPrefix === z) * (vx === vxPrefix ++ vxPostfix) *
    (map f vxPostfix === joinList xs)
splitMapJoin [] xs f vx pp = [] ## vx ## ((Refl && Refl) && pp)
splitMapJoin (z :: ys) xs f (w :: zs) pp =
  let (r1 ## r2 ## (r3 && r4)) = splitMapJoin ys xs f zs (splitCons pp).π2
  in (w :: r1) ## r2 ## ((cong2 (::) (splitCons pp).π1 r3.π1 && (cong (w ::) r3.π2)) && r4)

getJoin : {0 x, y : Type} -> (f : x -> y) ->
   (vx : (List x)) ->
   (vy : List (List y)) ->
   (pp : mapImpl f vx = joinList vy) ->
   List (List x)
getJoin f vx [] pp = []
getJoin f vx (z :: xs) pp =
  let sp : ?
      sp = splitMapJoin z xs f vx pp
  in sp.π1 :: getJoin f sp.π2.π1 xs sp.π2.π2.π2

0 proof1 :
  {0 x, y : Type} ->
  (f : x -> y) ->
  (c2 : List (List y)) ->
  (c1 : List x) ->
  (cm : mapImpl f c1 = joinList c2) ->
  joinList (getJoin f c1 c2 cm) = c1
proof1 f [] [] Refl = Refl
proof1 f (w :: xs) c1 cm with (splitMapJoin w xs f c1 cm)
  proof1 f (w :: xs) c1 cm | (p1 ## p2 ## ((p3 && p4) && p5)) = trans (cong (p1 ++) (proof1 f xs p2 p5 )) (sym p4)

proof2 :
    {a, b : Type} ->
    (f : a -> b) ->
    (c2 : List (List b)) ->
    (c1 : List a) ->
    (prf : mapImpl f c1 = joinList c2) ->
    map (map f) (getJoin f c1 c2 prf) = c2
proof2 f [] c1 cm = Refl
proof2 f (x :: xs) (ys) cm with (splitMapJoin x xs f ys cm)
  proof2 f (x :: xs) (ys) cm | (p1 ## p2 ## ((p3 && p4) && p5))
    = cong2 (::) p3 (proof2 f xs p2 p5)

getJoinPrf :
  {a, b : Type} ->
  {xs : List a} ->
  {xs' : List (List b)} ->
  {f : a -> b} ->
  {prf1 : map f xs = joinList xs'} ->
  {prf2 : map f xs = joinList xs'} ->
  ListEq (getJoin f xs xs' prf1) (getJoin f xs xs' prf2)
getJoinPrf {xs' = []} = SameNil
getJoinPrf {xs' = (x :: ys)} with (UIP prf1 prf2)
  getJoinPrf {xs' = (x :: ys)} | Refl with (splitMapJoin x ys f xs prf2)
    getJoinPrf {xs' = (x :: ys)} | Refl | (p1 ## p2 ## ((p3 && p4) && p5))
      = SameCons p1 p1 Refl getJoinPrf


getJoinEq :
  {a, b : Type} ->
  {xs, ys : List a} ->
  {xs' : List (List b)} ->
  {f : a -> b} ->
  (xs === ys) ->
  {prf1 : map f xs = joinList xs'} ->
  {prf2 : map f ys = joinList xs'} ->
  (getJoin f xs xs' prf1) === (getJoin f ys xs' prf2)
getJoinEq Refl with (UIP prf1 prf2)
  getJoinEq Refl | Refl = Refl

joinMapMap : {a, b : Type} ->
             {f : a -> b} ->
             (xs : List (List a)) ->
             (prf : map f (joinList xs) = joinList (map (map f) xs)) ->
             (getJoin f (joinList xs) (map (map f) xs) prf) `ListEq` xs
joinMapMap [] prf = SameNil
joinMapMap (x :: xs) prf with (splitMapJoin (map f x) (map (map f) xs) f (x ++ joinList xs) prf)
  joinMapMap (x :: xs) prf | (p1 ## p2 ## ((p3 && p4) && p5))
    = let (px, py) = splitConcat p3 (sym p4)
        ; rrr = joinMapMap {f} xs (trans (cong (map f) (sym py)) p5)
        ; sss = getJoinEq {f} (py) {xs' = map (map f) xs}
      in SameCons p1 x px (transitive (fromEq sss) rrr)

ListIsCartesianMonad : CartesianMonad Set ListIsFunctor
ListIsCartesianMonad = MkCartMonad
  ListIsMonad
  (\x, y, f => MkPullback x singleton f Refl
      (\x', cn , v' => getHead {a = x, b = y, f, y = cn.q_2 v'} (cn.q_1 v') (app cn.commutes v')
      )
      (\z => (\cone =>
                coneEqToEq $ MkConeEq
                    (funExt $ \w => getHeadElem (cone.q_1 w))
                    (funExt $ \w => mapSingletonF (cone.q_1 w) (app cone.commutes w) )) &&
              (\n' => funExt $ \zz  => Refl) )
  )
  (\x, y, f => MkPullback
      (List (List x))
      joinList
      (map (map f))
      (ListIsMonad .mult .commutes x y f )
      (\x', cone, v' => getJoin f (cone.q_1 v') (cone.q_2 v') (app cone.commutes v'))
      (\z => (\cone =>
                coneEqToEq $ MkConeEq
                    (funExt $ \cx : z => proof1 f (cone.q_2 cx) (cone.q_1 cx) (app cone.commutes cx))
                    (funExt $ \cx => let xx = proof2 f (cone.q_2 cx) (cone.q_1 cx) (app cone.commutes cx) in xx)
              ) &&
              (\vz => funExt $ \vb => listEqToEq $ joinMapMap (vz vb) ?)
      )
  )

transportMonad : (f, g : Endo Set) -> (x : Type) -> GenIso (Endo Set) (=>>) NTEq f g -> Monad Set f -> Monad Set g
transportMonad f g x (MkGenIso to from foFrom fromTo) (MkMonad u m mp id1 id2 )
  = MkMonad
  (u ⨾⨾⨾ to)
  (from -⨾- from ⨾⨾⨾ m ⨾⨾⨾ to)
  (\x => ?transportMonad_rhs3)
  ?transportMonad_rhs4
  ?transportMonad_rhs5

