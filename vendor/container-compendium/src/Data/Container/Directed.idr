module Data.Container.Directed

import Data.Container
import Data.Container.Category
import Data.Container.Morphism
import Data.Product
import Data.Coproduct
import Data.Category.Monoid
import Data.Category.Functor
import Data.Category.Bifunctor

%default total

%hide Prelude.Functor
%hide Prelude.MkFunctor

export
record Directed (0 c : Container) where
  constructor MkDirected
  act : (s : c.shp) -> c.pos s -> c.shp
  root : {s : c.shp} -> c.pos s
  ctx : {s: c.shp} -> (p : c.pos s) -> c.pos (act s p) -> c.pos s
  unitL : {s : c.shp} -> act s (root {s}) === s

--
-- ||| Unit container is a directed container
-- export
-- unitDirected : Directed CUnit
-- unitDirected = MkDirected
--   { act = \ _, _ => ()
--   , root = ()
--   , ctx = \_, _ =>  ()
--   , unitL = ?unitLUnit
-- }
--
-- ||| from any constant container with a monoidal structure emerges a directed container
-- export
-- monoidDirected : {ty : Type} -> Monoid ty => Directed (Const ty)
-- monoidDirected = MkDirected
--   { act = \_ => id
--   , root = neutral
--   , ctx = (<+>)
--   , unitL = ?unitLMonoid
--   }
--
-- export
-- productDirected : {c1 : Container} -> {c2 : Container} -> Directed c1 -> Directed c2 ->
--       Directed (c1 ⊗ c2)
-- productDirected d1 d2 = MkDirected
--   { act = \a => bimap (act d1 a.π1) (act d2 a.π2)
--   , root = rootPair
--   , ctx = \(p && p') => bimap (ctx d1 p) (ctx d2 p')
--   , unitL = ?unitLproduct
--   }
--   where
--     rootPair : {s : c1.shp * c2.shp} -> c1.pos s.π1 * c2.pos s.π2
--     rootPair = root d1 {s=s.π1} && root d2 {s = s.π2}
--
-- export
-- rightUnit : {c1 : Container} -> Directed c1 -> Directed (c1 * CUnit)
-- rightUnit d1 = MkDirected
--   { act = \a => \case (<+ x) => act d1 a.π1 x && a.π2
--                       (+> x) => a.π1 && ()
--   , root = +> ()
--   , ctx = \case (<+ x) => \case (<+ q) => <+ x
--                                 (+> q) => <+ x
--                 (+> x) => \case (<+ q) => <+ q
--                                 (+> q) => +> ()
--   , unitL = ?unitLRight
--   }


toComonoid : (d : Directed c) -> ComonoidObject {o = Container} {cat = Cont} {mon = composeMonoidal}

dup : Directed c -> c =%> c * c
dup dir = MkMorphism dup (\x => \case (<+ y) => y
                                      (+> y) => y)

counit : Directed c -> c =%> CUnit
counit (MkDirected act root ctx unitL) = MkMorphism (\_ => ()) (\x, _ => root)
