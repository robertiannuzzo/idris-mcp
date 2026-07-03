module Data.Category.Pullback

import Data.Category
import Data.Product
import Data.Iso
import Data.Sigma

import Data.Category.Set

import Proofs

%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)
%unbound_implicits off
public export
record Span {0 o : Type} {c : Category o} where
  constructor MkSpan
  o1, o2, apex : o
  f : o1 ~> apex
  g : o2 ~> apex
public export
record Cone {0 o : Type} {c : Category o} (0 s : Span {o, c}) (tip : o) where
  constructor MkCone
  q_1 : tip ~> s.o1
  q_2 : tip ~> s.o2
  commutes : (q_1 |> s.f) {a = tip, b = s.o1, c = s.apex} === (q_2 |> s.g) {a = tip, b = s.o2, c = s.apex}
public export
record ConeEq {0 o : Type} {c : Category o} {s : Span {o, c}} {t : o} (c1, c2 : Cone {o, c} s t) where
  constructor MkConeEq
  sameq1 : c1.q_1 === c2.q_1
  sameq2 : c1.q_2 === c2.q_2

export
coneEqToEq : {0 o : Type} -> {c : Category o} ->  {s : Span {o, c}} -> {t : o} ->
             {c1, c2 : Cone {o, c} s t} ->
             ConeEq c1 c2 -> c1 === c2
coneEqToEq {c1 = MkCone _ _ _} {c2 = MkCone _ _ _} (MkConeEq Refl Refl)
    = cong (MkCone ? ?) (UIP _ _)
public export
record Pullback {0 o : Type} {c : Category o} (s : Span {o, c}) where
  constructor MkPullback
  0 p : o
  p_1 : p ~> s.o1
  p_2 : p ~> s.o2
  0 square : (p_1 |> s.f) {a = p, b = s.o1, c = s.apex} ===
             (p_2 |> s.g) {a = p, b = s.o2, c = s.apex}
  prop_inverse : (x : o) -> Cone s x -> x ~> p
  0 inverses : let
    0 prop : (x : o) -> x ~> p -> Cone s x
    prop x m = MkCone (m |> p_1) (m |> p_2) (trans (sym $ c.compAssoc ? ? ? ? m p_1 s.f) $
                                             trans (cong ((|:>) c m) square) (c.compAssoc ? ? ? ? m p_2 s.g) )
    in (x : o) -> ((cone : Cone s x) -> prop x (prop_inverse x cone) === cone)
                * ((mor : x ~> p) -> prop_inverse x (prop x mor) === mor)
SigmaPullback : {a, b, c : Type} -> (f : a -> c) -> (g : b -> c) -> Pullback {c = Set} (MkSpan a b c f g)
SigmaPullback f g = MkPullback
    (Σ (x : a) | Σ (y : b) | f x === g y)
    π1
    (.π2.π1)
    (funExt $ \v => v.π2.π2)
    (\xty , cn, vx => cn.q_1 vx ## cn.q_2 vx ## app cn.commutes vx)
    (\vx => (\(MkCone q1 q2 sq) => cong (MkCone q1 q2) (UIP _ _))
         && (let
                 fnProof : (xx : vx -> Σ a (\x => Σ b (\y => f x = g y))) ->
                   (vy : vx) ->
                   ((xx vy) .π1 ## (((xx vy) .π2) .π1 ## app (trans Refl (trans (cong (\g, x => g (xx x)) (funExt (\v => (v .π2) .π2))) Refl)) vy)) = xx vy
                 fnProof xx vy with (xx vy) proof pq
                   fnProof xx vy | (p1 ## p2 ## p3) = cong ((p1 ##) . (p2 ##)) (UIP _ _)
              in \xx => funExt $ \yy => fnProof xx yy))
