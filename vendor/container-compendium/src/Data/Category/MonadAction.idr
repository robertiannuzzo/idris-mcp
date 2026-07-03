module Data.Category.MonadAction

import Data.Category
import Data.Category.Action
import Data.Category.Monad
import Data.Category.Monoid
import Data.Category.Functor
import Data.Category.Endofunctor
import Data.Category.Bifunctor
import Data.Category.Bifunctor.Apply
import Data.Category.NaturalTransformation

import Syntax.PreorderReasoning
import Pipeline.Equality

%hide Prelude.Ops.infixl.(*>)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Functor
%hide Prelude.(|>)

%unbound_implicits off
parameters
  (0 o1, o2: Type)
  (cat1 : Category o1)
  (cat2 : Category o2)
  (mon : Monoidal cat1)
  (act : LaxAction cat1 cat2 mon)
  (m : MonoidObject {o=o1} {cat=cat1} {mon})
  public export
  T : Endo cat2
  T = applyL m.obj act.laction
  unit : idF cat2 =>> T
  unit = act.lunitor ⨾⨾⨾ applyNT m.η act.laction
  -- the functor F'(x) = (m ⊗ m) ⊘ x
  F' : Endo cat2
  F' = applyL {a = cat1} ((m.obj ⊗ m.obj)) act.laction
  multAction : F' =>> T
  multAction = applyNT m.mult act.laction
  (⊘) : o1 -> o2 -> o2
  (⊘) x y = act.laction.mapObj (x && y)
  private infixr 3 ⊘

  (~⊘~) : {x, y : o1} -> {z, w : o2} -> (x ~> y) {cat=cat1} -> z ~> w -> x ⊘ z ~> y ⊘ w
  (~⊘~) m1 m2 = act.laction.mapHom (x && z) (y && w) (m1 && m2)
  private infixr 3 ~⊘~

  actor : (x, y : o1) -> (z : o2) -> x ⊘ (y ⊘ z) ~> (x ⊗ y) ⊘ z
  actor x y z = act.lactor.component (x && (y && z))

  unitor : (x : o2) -> x ~> mon.i ⊘ x
  unitor x = act.lunitor.component x

  private infixr 3 ⊘>

  -- This could be done with careful composition of act.lactor and some lemmas about apply
  -- but writing out the definition is actually easier
  appActor : T ⨾⨾ T =>> F'
  appActor = MkNT
    (\v => actor m.obj m.obj v)
    (\x, y, h => let
      0 steps : CongPipeline ? ?
      steps =
         Cong (\vx =>
            (actor m.obj m.obj x) |>
            (vx ~⊘~ h))
              [ cat1.id (m.obj ⊗ m.obj)
              , cat1.id m.obj -⊗- cat1.id m.obj]
         >| ((cat1.id m.obj ~⊘~ (cat1.id m.obj ~⊘~ h)) |>
            (actor m.obj m.obj y))
         :: Nil
      in runProof steps
        [ sym (mon.mult.presId (m.obj && m.obj))
        , act.lactor.commutes
            (m.obj && (m.obj && x))
            (m.obj && (m.obj && y))
            (cat1.id m.obj && (cat1.id m.obj && h))
        ]
    )
  mult : T ⨾⨾ T =>> T
  mult = appActor ⨾⨾⨾ multAction
  0 square : (x : o2) -> let
      0 top : T .mapObj (T .mapObj (T .mapObj x)) ~> T .mapObj (T .mapObj x)
      top = T .mapHom _ _ (mult.component x)
      0 bot, right : T .mapObj (T .mapObj x) ~> T .mapObj x
      right = mult.component x
      bot = mult.component x
      0 left : T .mapObj (T .mapObj (T .mapObj x)) ~> T .mapObj (T .mapObj x)
      left = mult.component (T .mapObj x)
      0 arm2, arm1 : T .mapObj (T .mapObj (T .mapObj x)) ~> T .mapObj x
      arm1 = (top |> right) {cat = cat2}
      arm2 = left |> bot
      in arm1 === arm2
  square x = Calc $
    |~
       (
         (cat1.id m.obj
           ~⊘~
         (actor m.obj m.obj x
           |>
         (m.mult ~⊘~ cat2.id x))))
       |>
         ((actor m.obj m.obj x)
           |>
           (m.mult ~⊘~ cat2.id x))
    ~~ ((actor m.obj m.obj (m.obj ⊘ x))
         |>
         (m.mult ~⊘~ cat2.id (m.obj ⊘ x)))
       |>
       ((actor m.obj m.obj x)
         |>
         (m.mult ~⊘~ cat2 .id x))
    ...(?squarePrf)



  0 identityLeft : (x : o2) -> let
      0 compose : T .mapObj x ~> T .mapObj x
      compose = (unit.component (T .mapObj x) |> mult.component x) {cat = cat2}
      0 straight : T .mapObj x ~> T .mapObj x
      straight = cat2.id (T .mapObj x)
      in compose === straight
  identityLeft x = Calc $
    |~ ((unitor (m.obj ⊘ x))
         |>
        (m.η ~⊘~ cat2.id (m.obj ⊘ x)))
      |>
       ((actor m.obj m.obj x)
         |>
        (m.mult ~⊘~ cat2.id x))
    ~~ cat2.id (m.obj ⊘ x)
    ...(?bee)

  0 identityRight : (x : o2) -> let
      0 compose : T .mapObj x ~> T .mapObj x
      compose = (T .mapHom _ _ (unit.component x) |> mult.component x) {cat = cat2}
      0 straight : T .mapObj x ~> T .mapObj x
      straight = cat2.id (T .mapObj x)
      in compose === straight
  identityRight x = Calc $
    |~
       (cat1.id m.obj ~⊘~ ((unitor x) |> (m.η ~⊘~ cat2.id x)))
       |>
       (
         (actor m.obj m.obj x)
         |>
         ((m.mult ~⊘~ cat2.id x))
       )
    ~~ cat2 .id (m.obj ⊘ x)
    ...(?idRPrf)
  public export
  MonadFromLaxAction : Monad cat2 T
  MonadFromLaxAction = MkMonad unit mult square identityLeft identityRight
