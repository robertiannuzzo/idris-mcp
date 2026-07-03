module Data.Category.Set

import Data.Category
import Data.Category.Monoid
import Data.Category.Bifunctor
import Data.Category.Functor
import Data.Category.Endofunctor
import Data.Category.Product
import Data.Category.NaturalTransformation
import Data.Category.Bicategory

import Data.Product
import Data.Sigma

import Proofs

---------------------------------------------------------------------------------
-- set is monoidal with cartesian product
---------------------------------------------------------------------------------
public export
SetMonoidal : Monoidal Set
SetMonoidal = MkMonoidal
  multFunctor
  Unit
  alpha
  leftUnitor
  rightUnitor
  where
    multFunctor : Bifunctor Set Set Set
    multFunctor = MkFunctor
      (uncurry (*))
      (\_, _ => uncurry bimap )
      (\x => funExt $ \(x && y) => Refl)
      (\_, _, _, f, g => Refl)

    psi : (v : Type * (Type * Type)) ->
          v.π1 * (v.π2.π1 * v.π2.π2) -> (v.π1 * v.π2.π1) * v.π2.π2
    psi v x = (x.π1 && x.π2.π1) && x.π2.π2

    phi : (v : Type * (Type * Type)) ->
          (v .π1 * (v .π2) .π1) * (v .π2) .π2 ->
          v .π1 * ((v .π2) .π1 * (v .π2) .π2)
    phi v x = x.π1.π1 && (x.π1.π2 && x.π2)

    alpha : let 0 f1, f2 : (Set × (Set × Set)) ->> Set
                f1 = (pair {a = Set, b = Set, c = Set × Set, d = Set} (idF _) multFunctor )
                   ⨾⨾ multFunctor
                f2 = assocR {a = Set, b = Set, c = Set}
                   ⨾⨾ ((pair {a = Set × Set} multFunctor (idF Set)) ⨾⨾ multFunctor)
            in f1 =~= f2
    alpha = MkNaturalIsomorphism
              (MkNT psi (\a, b, m => Refl))
              (MkNT phi (\_, _, _ => Refl))
              (\xv => funExt $ \(ys && (ys2 && ys3)) => Refl)
              (\xn => funExt $ \((y1 && y2) && y3) => Refl)

    leftUnitor :
        let 0 leftAppliedMult : Endo Set
            leftAppliedMult = unitL ⨾⨾ pair (Const Unit Set) (idF Set) ⨾⨾ multFunctor
        in leftAppliedMult =~= idF Set
    leftUnitor = MkNaturalIsomorphism
      (MkNT (\_ => π2) (\x, y, m => Refl))
      (MkNT (\x, y => MkUnit && y) (\_, _, _ => Refl))
      (\_ => funExt $ \(MkUnit && v2) => Refl)
      (\_ => Refl)

    rightUnitor :
        let 0 rightAppliedMult : Endo Set
            rightAppliedMult = unitR ⨾⨾ pair (idF Set) (Const Unit Set) ⨾⨾ multFunctor
        in rightAppliedMult =~= idF Set
    rightUnitor = MkNaturalIsomorphism
        (MkNT (\_ => π1) (\x, y, m => Refl))
        (MkNT (\_, x => x && MkUnit) (\_,_,_ => Refl))
        (\_ => funExt $ \(v && ()) => Refl)
        (\_ => Refl)
