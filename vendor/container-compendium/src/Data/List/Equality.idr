module Data.List.Equality

import Proofs
import Data.List.Quantifiers
public export
data ListAllEq : {0 a : Type} -> {0 p : a -> Type} -> {0 q : a -> Type} ->
                 {ls : List a} -> {0 prf : p ≡ q} ->
                 All p ls -> All q ls -> Type where
  AllEmpty : ListAllEq [] []
  AllCons : {0 a : Type} -> {0 p : a -> Type} -> {0 q : a -> Type} ->
            {ls : List a} -> {v1 : a} -> (x : p v1) -> (y : q v1) ->
            {xs : All p ls} -> {ys : All q ls} ->
            {prf : p ≡ q} ->
            {prf2 : x ≡ replace {p = \f => f v1} (sym prf) y} ->
            ListAllEq {a, p, q, ls, prf} xs ys ->
            ListAllEq {a, p, q, ls = v1 :: ls, prf} (x :: xs) (y :: ys)
export
listAllEqToEq :
    {0 a : Type} -> {0 p : a -> Type} -> {0 q : a -> Type} -> {prf : p ≡ q} ->
    {ls : List a} -> {xs : All p ls} -> {ys : All q ls} ->
    ListAllEq {ls, prf} xs ys -> ys ≡ replace {p = \vx => All vx ls} prf xs
listAllEqToEq {ls = [], prf = Refl} AllEmpty = Refl
listAllEqToEq {ls = y :: zs} (AllCons {prf = Refl, prf2 = Refl} z z w)
    = cong (z ::) (listAllEqToEq w)
