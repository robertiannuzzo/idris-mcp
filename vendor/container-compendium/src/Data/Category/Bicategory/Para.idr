module Data.Category.Bicategory.Para

import Data.Category
import Data.Category.Bicategory
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Bifunctor
import Data.Category.Set
import Data.Category.Monoid
import Data.Sigma

private infixr 0 ~@>
private infixr 1 |@>
private infixl 8 *@*

public export
ParaConstr : forall o. (cat : Category o) -> Monoidal cat -> Bicategory o
ParaConstr
  (MkCategory m i c idl idr ass)
  (MkMonoidal
    (MkFunctor combine combineMap combId combComp)
    _
    (MkNaturalIsomorphism _ phi _ _)
    _
    _
  ) =
  MkBiCat
    (\x, y => Σ o (\mx => combine (mx && x) `m` y) )
    (\x, y => MkCategory
        (one_cell x y)
        (\x => i x.π1) c
        (\_, _, _ => idl _ _ _)
        (\_, _, _ => idr _ _ _)
        (\a, b, c, d, f, g, h => ass _ _ _ _ _ _ _))
    (\_, _, _ => MkFunctor
      (\x => x.π2.π1 *@* x.π1.π1 ##
                    (phi.component (x.π2.π1 && (x.π1.π1 && _)) |@>
                    combineMap _ _ (i x.π2.π1 && x.π1.π2) |@>
                    x.π2.π2))
      (\f, g, h => combineMap _ _ (swap h))
      (\f => combId _)
      (\a, b, c, f, g => combComp _ _ _ _ _)
      )

    where
      0 (~@>) : o -> o -> Type
      (~@>) = m
      (*@*) : o -> o -> o
      (*@*) a b = combine (a && b)

      (|@>) : {a, b, c : o} -> m a b -> m b c -> m a c
      (|@>) = c
      0 one_cell : (a, b : o) ->
                   Σ o (\mx => mx *@* a ~@> b) ->
                   Σ o (\mx => mx *@* a ~@> b) -> Type
      one_cell a b m1 m2 = m1.π1 ~@> m2.π1
setPara : Bicategory Type
setPara = ParaConstr Set SetMonoidal
