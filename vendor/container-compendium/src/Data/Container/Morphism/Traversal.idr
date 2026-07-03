import Data.Boundary
import Data.Sigma
import Data.Vect
import Data.Product
import Data.Iso

import Data.Container
import Data.Container.Descriptions.List
import Data.Container.Morphism
import Data.Container.Morphism.Closed

import Proofs.Extensionality
import Proofs.Congruence
import Proofs.Sigma
record Traversal (a, b : Boundary) where
  constructor MkTraversal
  extract : a.π1 -> Σ Nat (\n => Vect n b.π1 * (Vect n b.π2 -> a.π2))
---------------------------------------------------------------------------------
-- Traversal is isomorphic to the List Monad on Container
---------------------------------------------------------------------------------

vectToFn : {0 a : Type} -> {0 m : Nat} -> Vect m a -> Fin m -> a
vectToFn v i = index i v

fnToVect : {0 a : Type} -> {m : Nat} -> (Fin m -> a) -> Vect m a
fnToVect f {m = 0} = []
fnToVect f {m = (S k)} = f FZ :: fnToVect (f . FS)

vecIso : {0 a : Type} -> {n : Nat} -> Vect n a `Iso` (Fin n -> a)
vecIso = MkIso
  vectToFn
  fnToVect
  toFrom
  fromTo
  where
    fromTo : {0 n : Nat} -> (x : Vect n a) -> fnToVect (vectToFn x) === x
    fromTo [] = Refl
    fromTo (x :: xs) = cong (x ::) (fromTo xs)

    0 toFrom : {m : Nat} -> (fn : Fin m -> a) -> vectToFn {m} (fnToVect {m} fn) === fn
    toFrom {m = 0} fn = funExt $ \w => absurd w
    toFrom {m = (S k)} fn = funExt go
      where
        go : (w : Fin (S k)) -> index w (fn FZ :: fnToVect (\y => fn (FS y))) = fn w
        go FZ = Refl
        go (FS x) = app (vectToFn (fnToVect (fn . FS))) (fn . FS) (toFrom (fn . FS)) x

%unbound_implicits on
listIsTraversal : (a :- a') =%> ListCont ▶ (b :- b') -> Traversal (MkB a a') (MkB b b')
listIsTraversal (MkMorphism fwd bwd) = MkTraversal $ \x => (fwd x).ex1 ## (vecIso.from (fwd x).ex2 && \vx => bwd x (vecIso.to vx))

traversalIsList : Traversal (MkB a a') (MkB b b') -> (a :- a') =%> ListCont ▶ (b :- b')
traversalIsList (MkTraversal e) = MkMorphism
  (\x => MkEx (e x).π1 (vecIso.to (e x).π2.π1))
  (\x, f => (e x).π2.π2 (vecIso.from f))

lemma : {0 a : Type} -> (f : a -> TyList b) -> (x : a) -> MkEx (f x).ex1 (vectToFn {a=b, m = (f x).ex1} (fnToVect {a=b, m = (f x).ex1} ((f x).ex2))) === (f x)
lemma f x with (f x)
  lemma f x | (MkEx n m) = cong (MkEx n) (vecIso.toFrom m)

traversalIso : ((a :- a') =%> ListCont ▶ (b :- b')) `Iso` (Traversal (MkB a a') (MkB b b'))
traversalIso = MkIso
  listIsTraversal
  traversalIsList
  pp
  qq
  where
    pp : (zv : Traversal (MkB a a') (MkB b b')) -> listIsTraversal (traversalIsList zv) === zv
    pp (MkTraversal ex) = cong MkTraversal $ funExt $ fg
    where
      fg : (z : a) -> ? === ex z
      fg z with (ex z) proof prf
        fg z | (0 ## ([] && p)) = rewrite sym $ proj1 prf in
              cong2Dep (##) Refl $
              cong2 Product.(&&)
                       { a = fnToVect (vectToFn (((ex z) .π2) .π1))
                       , b = replace {p = \nm => Vect nm b} (sym $ proj1 prf) []
                       , c = (\vx => (ex z).π2.π2 (fnToVect (vectToFn vx)))
                       , d = replace {p = \nm => Vect nm b' -> a'} (sym $ proj1 prf) p}
                       (rewrite prf in Refl)
                       (funExt $ \vx => rewrite vecIso.fromTo vx in rewrite prf in Refl)
        fg z | ((S k) ## (xs && p)) = rewrite sym $ proj1 prf in
              cong2Dep' (##) Refl $
              cong2 Product.(&&)
                  { a = fnToVect (vectToFn (((ex z) .π2) .π1))
                  , b = replace {p = \nm => Vect nm b} (sym $ proj1 prf) xs
                  , c = (\vx => (ex z).π2.π2 (fnToVect (vectToFn vx)))
                  , d = replace {p = \nm => Vect nm b' -> a'} (sym $ proj1 prf) p}
                  (rewrite vecIso.fromTo (((ex z) .π2) .π1) in rewrite prf in Refl)
                  (funExt $ \vx => rewrite vecIso.fromTo vx in rewrite prf in Refl)

    0 qq : (x : (a :- a') =%> (ListCont ▶ (b :- b'))) -> traversalIsList (listIsTraversal x) === x
    qq (MkMorphism f b) = cong2Dep' MkMorphism
        (funExt $ lemma f)
        (funExtDep $ \v => funExt $ \w => cong (b v) (vecIso.toFrom w))
