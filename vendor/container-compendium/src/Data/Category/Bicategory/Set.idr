import Data.Category
import Data.Category.Bicategory
import Data.Category.Bifunctor
import Data.Category.Functor
import Data.Category.Functor.Category
import Data.Category.NaturalTransformation

import Syntax.PreorderReasoning

import Data.Sigma

horzId : {o1, o2, o3 : Type} ->
    {a : Category o1} -> {b : Category o2} -> {c : Category o3} ->
    (f1 : a ->> b) -> (f2 : b ->> c) ->
    identity {f = f1} -⨾- identity {f = f2} `NTEq` identity {f = f1 ⨾⨾ f2}
horzId (MkFunctor fo1 fm1 fi1 fc1) (MkFunctor fo2 fm2 fi2 fc2) = MkNTEq $ \x =>  Calc $
    |~ (|:>) c (fm2 (fo1 x) (fo1 x) (b.id (fo1 x))) (fm2 (fo1 x) (fo1 x) (fm1 x x (a.id x)))
    ~~ (|:>) c (c.id (fo2 (fo1 x))) (fm2 (fo1 x) (fo1 x) (fm1 x x (a.id x)))
        ...(cong (\xn => (|:>) c xn (fm2 (fo1 x) (fo1 x) (fm1 x x (a.id x))))
                (fi2 (fo1 x)))
    ~~ fm2 (fo1 x) (fo1 x) (fm1 x x (a.id x)) ...(c.idLeft _ _ _)

horizontalMorNT : (a, b, c : Σ Type Category) ->
                  Bifunctor (FunctorCat a.π2 b.π2) (FunctorCat b.π2 c.π2) (FunctorCat a.π2 c.π2)
horizontalMorNT (o1 ## c1) (o2 ## c2) (o3 ## c3) = MkFunctor
    (uncurry (⨾⨾))
    (\f1, f2, m => m.π1 -⨾- m.π2)
    (\(f1 && f2) => ntEqToEq $ horzId f1 f2)
    (\a, b, c, f, g => sym $ ntEqToEq $ interchange _ _ _ _)

SetBicategory : Bicategory (Σ Type Category)
SetBicategory = MkBiCat
    (\x, y => x.π2 ->> y.π2)
    (\x, y => FunctorCat x.π2 y.π2)
    horizontalMorNT
