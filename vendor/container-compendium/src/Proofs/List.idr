module Proofs.List


import Data.List.Quantifiers
import Proofs.Relation
import Proofs.Congruence

export
prfHead : {x, y : a} -> {xs, ys : List a} -> (x :: xs) === (y :: ys) -> x === y
prfHead Refl = Refl

export
prfTail : {x, y : a} -> {xs, ys : List a} -> (x :: xs) === (y :: ys) -> xs === ys
prfTail {xs} Refl = Refl

export
splitConcat :
   {a, b : Type} ->
   {xs, ys, xs', ys' : List a} ->
   {f : a -> b} ->
   (sameMap : map f xs = map f ys) ->
   (catPrf : xs ++ xs' = ys ++ ys') ->
   (xs === ys, xs' === ys')
splitConcat {xs = []} {ys = []} sameMap catPrf = (Refl, catPrf)
splitConcat {xs = []} {ys = (x :: xs)} Refl catPrf impossible
splitConcat {xs = (x :: xs)} {ys = []} Refl catPrf impossible
splitConcat {xs = (x :: xs)} {ys = y :: ys} sameMap catPrf
  = let rec = splitConcat {xs} {ys} {f} (prfTail sameMap) (prfTail catPrf) in mapFst (\xx => cong2 (::) (prfHead catPrf) xx) rec

public export
data ListEq : (xs, ys : List a) -> Type where
  SameNil : ListEq [] []
  SameCons : (x, y : a) -> x === y -> ListEq xs ys -> ListEq (x :: xs) (y :: ys)

public export
listEqToEq : ListEq xs ys -> xs === ys
listEqToEq SameNil = Refl
listEqToEq (SameCons x y prf z) = cong2 (::) prf (listEqToEq z)

export
fromEq : {xs : List a} -> xs === ys -> ListEq xs ys
fromEq {xs = []} Refl = SameNil
fromEq {xs = (x :: xs)} Refl = SameCons x x Refl (fromEq Refl)

export
Reflexive (List a) ListEq where
  reflexive {x = []} = SameNil
  reflexive {x = (x :: xs)} = SameCons x x Refl reflexive

export
Transitive (List a) ListEq where
  transitive SameNil SameNil = SameNil
  transitive (SameCons x y p1 r) (SameCons y z p2 s)
    = let rec = transitive r s in SameCons x z (trans p1 p2) rec

export
Preorder (List a) ListEq where

export
EqRel (List a) ListEq where
  toEq = listEqToEq


namespace All
  public export
  data AllEq :
    {0 a : Type} -> (p : a -> Type) ->
    {0 ls, ks : List a} ->
    ListEq ls ks ->
    (xs : All p ls) ->
    (ys : All p ks) -> Type where
    SameNil : AllEq p SameNil [] []
    SameCons : {0 x : a} -> {0 p : a -> Type} ->
               {0 ls, ks : List a} ->
               {0 recList : ListEq ls ks} ->
               {0 xs : All p ls} -> {0 ys : All p ks} ->
               (v : p x) -> AllEq p recList xs ys -> AllEq p (SameCons x x Refl recList) (v :: xs) (v :: ys)

  public export 0
  allEqToEq :
    {ls : _} ->
    {xs : All p ls} ->
    {ys : All p ks} ->
    {prf : ListEq ls ks} ->
    (eq : AllEq p prf xs ys) -> xs === replace {p = All p} (sym $ listEqToEq prf) ys
  allEqToEq {ls = []} {xs = []} {ys = []} {prf = SameNil} SameNil = Refl
  allEqToEq {ls = (x :: ls)} {xs = (x :: xs)} {ys = (x :: ys)} {prf = .(SameCons x x Refl recList)} (SameCons x y)
    = rewrite allEqToEq y in rewrite listEqToEq recList in Refl

