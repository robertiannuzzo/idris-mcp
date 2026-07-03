module Data.Container.Closed.Coproduct

import Data.Container.Coproduct.Definition
import Data.Container.Closed
import Data.Container.Closed.Category

import Data.Category.Bifunctor

public export
(~+~) : a =&> a' -> b =&> b' -> (a + b) =&> (a' + b')
(~+~) m1 m2 = !! \x => ?dhhdh

public export
alternative : (c1, c2 : Container) -> Container
alternative c1 c2 = c1 + c2

public export
alternatively  : a =&> a' -> b =&> b' -> (a + b) =&> (a' + b')
alternatively = (~+~)

public export
CoprodContBifunctor : Bifunctor Cont Cont Cont
CoprodContBifunctor = MkFunctor
  (Product.uncurry (+))
  (\_, _, m => m.π1 ~+~ m.π2)
  ?presId
  ?presComp
  -- (\(x1 && x2) => depLensEqToEq $ MkDepLensEq bifunctorId'
  --     (\case (+> v) => \_ => Refl
  --            (<+ v) => \_ => Refl
  --     )
  -- )
  -- (\a, b, c, (f1 && f2), (g1 && g2) => depLensEqToEq $ MkDepLensEq
  --     (bimapCompose)
  --     (\case (<+ x) => \_ => Refl
  --            (+> x) => \_ => Refl))
public export
dia : a + a =&> a

public export
dia3 : a + a + a =&> a

public export
inr : b =&> a + b

public export
inl : a =&> a + b

