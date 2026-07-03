module Data.Category.Functor.Category

import Data.Category
import Data.Category.Functor
import Data.Category.Bifunctor
import Data.Category.NaturalTransformation

import Syntax.PreorderReasoning

%hide Prelude.Ops.infixl.(|>)
parameters
  {0 o1, o2 : Type}
  {0 c : Category o1} {0 d : Category o2}
  {f, g : c ->> d}
  0
  (|>>) : {x, y, z : o2} -> x ~> y -> y ~> z -> x ~> z
  (|>>) = (|:>) d
  private infixr 2 |>>
  public export
  ntIdentityRight :
    (n : f =>> g) -> NTEq (n ⨾⨾⨾ identity {f = g}) n
  ntIdentityRight nt = MkNTEq $ \vx => Calc $
      |~ nt.component vx |>> g.mapHom vx vx (c.id vx)
      ~~ nt.component vx |>> d.id (g.mapObj vx)
         ...(cong (nt.component vx |>>) (g.presId vx))
      ~~ nt.component vx
         ...((d.idRight _ _ _))
  public export
  0 ntIdentityLeft :
    (n : f =>> g) -> NTEq (NaturalTransformation.identity ⨾⨾⨾ n) n
  ntIdentityLeft nt = MkNTEq $ \v =>
      Calc $ |~ f.mapHom v v (c.id v) |>> nt.component v
             ~~ d.id (f.mapObj v)     |>> nt.component v
                ...(cong (|>> nt.component v) (f.presId v))
             ~~ nt.component v
                ...(d.idLeft _ _ (nt.component v))
  public export
  0 ntAssoc :
      {h, i : c ->> d} ->
      (n1 : f =>> g) -> (n2 : g =>> h) -> (n3 : h =>> i) ->
      NTEq (n1 ⨾⨾⨾ (n2 ⨾⨾⨾ n3)) ((n1 ⨾⨾⨾ n2) ⨾⨾⨾ n3)
  ntAssoc (MkNT n1 p1) (MkNT n2 p2) (MkNT n3 p3) = MkNTEq $ \v =>
      (d.compAssoc _ _ _ _ (n1 v) (n2 v) (n3 v))
public export
FunctorCat : (c1 : Category a) -> (c2 : Category b) -> Category (c1 ->> c2)
FunctorCat c1 c2 = MkCategory
    (=>>)
    (\f => identity {f})
    (⨾⨾⨾)
    (\f, g, n => ntEqToEq $ ntIdentityRight n)
    (\f, g, n => ntEqToEq $ ntIdentityLeft n)
    (\f, g, h, i, nt1, nt2, nt3 =>
        ntEqToEq $ ntAssoc nt1 nt2 nt3
    )
