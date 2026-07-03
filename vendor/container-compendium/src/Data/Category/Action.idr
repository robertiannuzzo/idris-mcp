module Data.Category.Action

import public Data.Category.Monoid
import public Data.Category.Bifunctor
import public Data.Category.NaturalTransformation

%hide Prelude.(&&)
%hide Prelude.Ops.infixl.(*>)

%unbound_implicits off
public export
record Action
  {0 o1, o2 : Type} (c : Category o1) (d : Category o2)
  (mon : Monoidal c) where
  constructor MkAction
  action : Bifunctor c d d
  actor : let 0 f1 : (c × (c × d)) ->> d
              f1 = pair (idF c) action ⨾⨾ action
              0 f2 : (c × (c × d)) ->> d
              f2 = assocR ⨾⨾ pair mon.mult (idF d) ⨾⨾ action
           in f1 =~= f2
  unitor : idF d =~= Bifunctor.applyL {a = c} mon.i action
public export
record LaxAction {0 o1, o2 : Type}
  (c : Category o1) (d : Category o2)
  (mon : Monoidal c) where
  constructor MkLaxAction
  laction : Bifunctor c d d
  lactor : let 0 f1, f2 : (c × (c × d)) ->> d
               f1 = pair (idF c) laction ⨾⨾ laction
               f2 = assocR ⨾⨾ pair mon.mult (idF d) ⨾⨾ laction
            in f1 =>> f2
  lunitor : idF d =>> Bifunctor.applyL {a = c} mon.i laction
public export
relax : {0 o1, o2 : Type} -> {c : Category o1} -> {d : Category o2} ->
        {0 mon : Monoidal c} ->
        Action c d mon -> LaxAction c d mon
relax act = MkLaxAction
    { laction = act.action
    , lactor = act.actor.nat
    , lunitor = act.unitor.nat
    }
public export
monoidalSelfAction : {0 cat : Category _} ->
    (mon : Monoidal cat) -> Action cat cat mon
monoidalSelfAction mon = MkAction
  { action = mon.mult
  , actor = mon.alpha
  , unitor = symNT (mon.leftUnitor)
  }
