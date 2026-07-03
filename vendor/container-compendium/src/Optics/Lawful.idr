module Optics.Lawful

import Data.Boundary
import Data.Product
import Data.Coproduct
import Data.Iso
import Data.Sigma
import Data.Container.Descriptions.Maybe
import Data.Container.Morphism
import Data.Container.Morphism.Accessor

record Traversal (a, b : Boundary) where
  constructor MkTraversal
  0 r1 : Type
  0 r2 : Type
  fwd : a.π1 -> r1 + (r2 * b.π1)
  bwd : r1 + (r2 * b.π2) -> a.π2


GeneralOptic : (s, a : Type) -> Type
GeneralOptic s a = Σ Type (\r => Iso s (r * a))

TraversalIso : (a, b : Type) -> Type
TraversalIso a b = Σ Type (\r => Σ Type (\s => Iso a (r + (s * b))))

record TraversalPlain (a, b : Type) where
  constructor MkPlain
  match : a -> a + b
  update : a * b -> a
  law1 : (x : a) -> (y : a) -> match x = <+ y -> (z : a * b) -> update z = y
  law2 : (x : a) -> (y : b) -> match x = +> y -> update (x && y) = x
  law3 : (x : a * b) -> (match (update x) = <+ x.π1) + (match (update x) = +> x.π2)

traversalIsoToTraversal : TraversalIso a b -> Traversal (MkB a a) (MkB b b)
traversalIsoToTraversal (r1 ## r2 ## (MkIso to from toFrom fromTo)) = MkTraversal r1 r2 to from


traversalIsoToPlain : TraversalIso a b -> TraversalPlain a b
traversalIsoToPlain (r1 ## r2 ## (MkIso to from toFrom fromTo)) =
  MkPlain ?traversalIsoToPlain_rhs_2 ?traversalIsoToPlain_rhs_3 ?traversalIsoToPlain_rhs_4 ?traversalIsoToPlain_rhs_5 ?traversalIsoToPlain_rhs_6

fromMonad : {a, b : Type} -> (a :- a) =%> MaybeCont ▶ (b :- b) -> TraversalIso a b
fromMonad (MkMorphism fwd bwd) = a ## (b -> a)  ## MkIso
    ff
    bb
    ?fb
    ?bf
  where
    ff : a -> a + ((b -> a) * b)
    ff xs with (fwd xs) proof p'
      ff xs | (MkEx False ex2) = <+ xs
      ff xs | (MkEx True ex2) = +> ((\ bn => bwd xs (\arg => ex2 (rewrite__impl (IsTrue . ex1) (sym p') arg))) && ex2 T)
    bb : a + ((b -> a) * b) -> a
    bb (<+ x) = x
    bb (+> x) = x.π1 x.π2

    fb : (x : a + ((b -> a) * b)) -> ff (bb x) === x
    fb (<+ x) with (fwd x)
      fb (<+ x) | (MkEx True ex2) = ?fb_rhs_0_rhs0_02
      fb (<+ x) | (MkEx False ex2) = ?fb_rhs_0_rhs0_0
    fb (+> x) = ?fb_rhs_1
    -- bf : (x : a) -> bb (ff x) === x

total
fromMonad' : {a, b : Type} -> (a :- a) =%> MaybeCont ▶ (b :- b) -> TraversalPlain a b
fromMonad' (MkMorphism fwd bwd) =
  MkPlain fwd' bwd' law1 ?fromMonad_rhs2_4 ?fromMonad_rhs2_5
  where
    fwd' : a -> a + b
    fwd' x with (fwd x)
      fwd' x | (MkEx True ex2) = +> ex2 T
      fwd' x | (MkEx False ex2) = <+ x
    bwd' : a * b -> a
    bwd' (x1 && x2) with (fwd x1) proof p
      bwd' (x1 && x2) | (MkEx True ex2) = bwd x1 (\xn => ex2 (replace {p = IsTrue . ex1} p xn))
      bwd' (x1 && x2) | (MkEx False ex2) = x1

    law1 : (x : a) -> (y : a) -> fwd' x = <+ y -> (z : a * b) -> bwd' z = y
    law1 x y prf z with (fwd x) proof p
      -- law1 x y prf z | (MkEx True ex2) = absurd prf
      law1 x x Refl (z1 && z2) | (MkEx False ex2) with (fwd z1) proof p'
        law1 x x Refl (z1 && z2) | (MkEx False ex2) | (MkEx True f) = ?law1_rhs_rhss_0A_rhsA_022bK
        law1 x x Refl (z1 && z2) | (MkEx False ex2) | (MkEx False f) = ?law1_rhs_rhss_0A_rhsA_0

