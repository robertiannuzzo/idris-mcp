module APLAS

import Data.Container
import Data.Container.Category
import Data.Container.Morphism
import Data.Container.Descriptions.Maybe
import Data.Container.Maybe
import Data.Container.Monad
import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Monad
import Data.Category.Monoid
import Data.Category.Bifunctor
import Data.Iso

import Data.Coproduct

import Proofs

import Syntax.PreorderReasoning
{- skip this file for the thesis

%hide Data.Container.Morphism.Context.State
%hide Data.Container.Morphism.Context.state
%hide Data.Container.Morphism.Context.costate
%hide Data.Container.Morphism.Context.Costate

%hide Prelude.Ops.infixl.(*>)
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.(<|)
%default total

namespace Containers
  namespace Definition1

    Container : Type
    Container = Σ Type (\req => req -> Type)

  namespace Definition2


    export
    record (=>>) (c1, c2 : Container) where
      constructor (<|)
      fwMap : c1.req -> c2.req
      bwMap : {x : c1.req} -> c2.res (fwMap x) -> c1.res x

  namespace Definition3

    (⨾) : {0 a, b, c : Container} -> a =>> b -> b =>> c -> a =>> c
    (⨾) (q1 <| r1) (q2 <| r2) = q2 . q1 <| r1 . r2

    -- In the rest of the program we are going to use =%> for container
    -- morphisms, it has an explicit first argument in the bwMap

namespace Definition4

  proposition4 : Category Container
  proposition4 = Cont

namespace Definition5

  maybeMap : Container -> Container
  maybeMap (c !> c') = (x : Maybe c) !> All c' x

namespace Proposition6

  maybeMapId : forall t. (v : Maybe t) -> Prelude.map (\x => x) v === v
  maybeMapId Nothing = Refl
  maybeMapId (Just x) = Refl

  maybeMapComp : forall a, b, c. (v : Maybe a) -> {f : b -> c} -> {g : a -> b} ->
                 Prelude.map (f . g) v === Prelude.map f (Prelude.map g v)
  maybeMapComp Nothing = Refl
  maybeMapComp (Just x) = Refl

  0
  MaybeAllIdrisPresId : forall a. MaybeAllIdrisFunctor (identity {a}) <%≡%> identity {a = All.Maybe a}
  MaybeAllIdrisPresId = MkDepLensEq maybeMapId maybeMapId'
    where

      maybeMapId' : (v : Maybe a.req) -> (y : All a.res (Prelude.map (\x => x) v)) ->
                    bwdMaybeAllF {x = a, y = a, mor = identity {a}} v y ===
                      replace {p = All a.res} (maybeMapId v) y
      maybeMapId' (Just x) (Yay y) = Refl
      maybeMapId' (Nothing) Nay = Refl

  public export
  MaybeAllIdrisPresComp : forall a, b, c. (f : a =%> b) -> (g : b =%> c) ->
                          MaybeAllIdrisFunctor (f ⨾ g) <%≡%>
                          MaybeAllIdrisFunctor f ⨾ MaybeAllIdrisFunctor g
  MaybeAllIdrisPresComp f g = MkDepLensEq
    (\v => maybeMapComp v)
    (\case Nothing => \Nay => Refl
           (Just x) => \(Yay y) => Refl)

  public export
  MaybeIsFunctor : Functor Cont Cont
  MaybeIsFunctor = MkFunctor
    All.Maybe
    (\_, _ => MaybeAllIdrisFunctor)
    (\_ => depLensEqToEq MaybeAllIdrisPresId)
    (\_, _, _, f, g => depLensEqToEq (MaybeAllIdrisPresComp f g))

namespace Proposition7

  unit : idF Cont =>> MaybeIsFunctor
  unit = MkNT
    maybeAllPure
    (\a, b, m => depLensEqToEq $ MkDepLensEq (\_ => Refl) (\v => \(Yay w) => Refl))

  mult : MaybeIsFunctor ⨾⨾ MaybeIsFunctor =>> MaybeIsFunctor
  mult = MkNT
    maybeAllJoin
    (\a, b, m => cong2Dep' (<!)
        (funExt $ \case (Just (Just x)) => Refl ; Just Nothing => Refl ; Nothing => Refl)
        (funExtDep $ \case (Just (Just x)) => funExt $ \(Yay x) => Refl
                         ; Nothing => funExt (\x => Refl)
                         ; Just Nothing => funExt (\x => Refl)))

  %unbound_implicits off
  joinMapJoin : forall a. (v : Maybe (Maybe (Maybe a))) -> maybeJoin (Prelude.map maybeJoin v) = maybeJoin (maybeJoin v)
  joinMapJoin Nothing = Refl
  joinMapJoin (Just Nothing) = Refl
  joinMapJoin (Just (Just Nothing)) = Refl
  joinMapJoin (Just (Just (Just x))) = Refl

  bwdJoinMapJoin : {0 x : Container} -> (v : Maybe (Maybe (Maybe x.req))) ->
                   (y : All x.res (maybeJoin (Prelude.map maybeJoin v))) ->
                   bwdMaybeAllF {mor = maybeAllJoin x} v (maybeAllJoinBwd (Prelude.map maybeJoin v) y) ===
                     maybeAllJoinBwd v (maybeAllJoinBwd (maybeJoin v) (replace {p = All x.res} (joinMapJoin v) y))
  bwdJoinMapJoin Nothing Nay = Refl
  bwdJoinMapJoin (Just Nothing) Nay = Refl
  bwdJoinMapJoin (Just (Just Nothing)) Nay = Refl
  bwdJoinMapJoin (Just (Just (Just z))) (Yay y) = Refl

  monadSquare : (x : Container) -> let
                left, top : All.Maybe (All.Maybe (All.Maybe x)) =%> All.Maybe (All.Maybe x)
                top = MaybeAllIdrisFunctor (maybeAllJoin x)
                left = maybeAllJoin (All.Maybe x)
                in top ⨾ maybeAllJoin x <%≡%> left ⨾ maybeAllJoin x
  monadSquare x = MkDepLensEq
      joinMapJoin
      bwdJoinMapJoin

  maybeJoinJust : forall a. (v : Maybe a) -> maybeJoin (Just v) = v
  maybeJoinJust Nothing = Refl
  maybeJoinJust (Just x) = Refl

  bwdMaybeJoinJust : forall x. (v : Maybe (x .req)) -> (y : All x.res (maybeJoin (Just v))) ->
                               Maybe.obtain (maybeAllJoinBwd (Just v) y)
                               = replace {p = All x.res} (maybeJoinJust v) y
  bwdMaybeJoinJust Nothing Nay = Refl
  bwdMaybeJoinJust (Just z) (Yay y) = Refl

  monadIdLeft : (x : Container) -> maybeAllPure (All.Maybe x) ⨾ maybeAllJoin x
                <%≡%> identity _
  monadIdLeft x = MkDepLensEq maybeJoinJust bwdMaybeJoinJust

  maybeJoinMapJust : forall a. (v : Maybe a) -> maybeJoin (Prelude.map Just v) = v
  maybeJoinMapJust Nothing = Refl
  maybeJoinMapJust (Just x) = Refl

  bwdMaybeJoinMapJust : forall x. (v : Maybe (x .req)) ->
                        (y : All x.res (maybeJoin (Prelude.map Just v))) ->
                        bwdMaybeAllF {mor = maybeAllPure x} v (maybeAllJoinBwd (Prelude.map Just v) y) ===
                          replace {p = All x.res} (maybeJoinMapJust v) y
  bwdMaybeJoinMapJust Nothing Nay = Refl
  bwdMaybeJoinMapJust (Just z) (Yay y) = Refl

  monadIdRight : (x : Container) -> MaybeAllIdrisFunctor (maybeAllPure x) ⨾ maybeAllJoin x <%≡%> identity {a = All.Maybe x}
  monadIdRight x = MkDepLensEq
      maybeJoinMapJust bwdMaybeJoinMapJust

  %unbound_implicits on

  public export
  maybeMonadInCont : Monad' Cont MaybeIsFunctor
  maybeMonadInCont = MkMonad'
      unit
      mult
      (\x => depLensEqToEq $ monadSquare x)
      (\x => depLensEqToEq $ monadIdLeft x)
      (\x => depLensEqToEq $ monadIdRight x)


namespace Definition8

  coproduct : Container -> Container -> Container
  coproduct c1 c2 = (x : c1.req + c2.req) !> choice c1.res c2.res x

namespace Proposition9

  -- Maybe and 1 + are isomorphic in the category of types
  maybeCoprod : Maybe x -> () + x
  maybeCoprod Nothing = <+ ()
  maybeCoprod (Just p2) = +> p2

  coprodMaybe : () + x -> Maybe x
  coprodMaybe (<+ y) = Nothing
  coprodMaybe (+> y) = Just y

  coprodMaybeCoprod : (v : () + x) -> maybeCoprod (coprodMaybe v) === v
  coprodMaybeCoprod (<+ ()) = Refl
  coprodMaybeCoprod (+> y) = Refl

  maybeCoprodMaybe : (v : Maybe x) -> coprodMaybe (maybeCoprod v) === v
  maybeCoprodMaybe Nothing = Refl
  maybeCoprodMaybe (Just y) = Refl

  maybeCoprodIso : {0 x : Type} -> Iso (Prelude.Maybe x) (() + x)
  maybeCoprodIso = MkIso maybeCoprod coprodMaybe coprodMaybeCoprod maybeCoprodMaybe

  -- Maybe and 1 + are isomorphic in the category of containers
  bwd_maybeToCoprod : (x : Maybe v.req) ->
                      choice (\value => Unit) v.res (maybeCoprod x) -> All v.res x
  bwd_maybeToCoprod Nothing y = Nay
  bwd_maybeToCoprod (Just x) y = Yay y

  bwd_coprodMaybe : (x : () + v.req) -> All v.res (coprodMaybe x) -> choice (\value => Unit) v.res x
  bwd_coprodMaybe (<+ x) y = ()
  bwd_coprodMaybe (+> x) y = obtain y

  export
  maybeToCoprod : (v : Container) -> All.Maybe v =%> End + v
  maybeToCoprod v = maybeCoprod <! bwd_maybeToCoprod

  export
  coprodToMaybe : (v : Container) -> End + v =%> All.Maybe v
  coprodToMaybe v = coprodMaybe <! bwd_coprodMaybe

  %unbound_implicits off
  coprodAndBack : (v : Container) -> coprodToMaybe v ⨾ maybeToCoprod v <%≡%> identity {a = End + v}
  coprodAndBack v = MkDepLensEq coprodMaybeCoprod
      (\case (<+ x) => \() => Refl
             (+> x) => \_ => Refl)

  maybeAndBack : (v : Container) -> maybeToCoprod v ⨾ coprodToMaybe v <%≡%> identity {a = All.Maybe v}
  maybeAndBack v = MkDepLensEq maybeCoprodMaybe
      (\case Nothing => \Nay => Refl
             (Just x) => \(Yay y) => Refl)

  coprodMaybeIsoCont : (x : Container) -> ContIso (All.Maybe x) (End + x)
  coprodMaybeIsoCont x = MkGenIso (maybeToCoprod x) (coprodToMaybe x) (maybeAndBack x) (coprodAndBack x)

%unbound_implicits on
namespace Definition10

  dia : a + a =%> a
  dia = dia <! (\case (+> r) => id ; (<+ l) => id)

namespace Definition11

  maybeU : All.Maybe End =%> End
  maybeU = maybeToCoprod End ⨾ dia

namespace Definition12

  public export
  (>>) : Container -> Container -> Container
  (>>) c1 c2 = (x : Σ c1.req (\r => c1.res r -> c2.req))
              !> Σ (c1.res x.π1) (\r => c2.res (x.π2 r))

namespace Definition13

  public export
  compLUnit : End >> c =%> c
  compLUnit = (\x => x.π2 ()) <! (\x, y => () ## y)

  public export
  compRUnit : c >> End =%> c
  compRUnit = (\x => x.π1) <! (\x, y => y ## ())

namespace Definition14

  public export
  data StarShp : Container -> Type where
    Done : forall c. StarShp c
    More : forall c. Ex c (StarShp c) -> StarShp c

  public export
  StarPos : (c : Container) -> StarShp c -> Type
  StarPos c Done = Unit
  StarPos c (More x) = Σ (c.res x.ex1) (\y => assert_total $ StarPos c (x.ex2 y))

  public export
  Kleene : Container -> Container
  Kleene c = (!>) (StarShp c) (StarPos c)

%unbound_implicits on
namespace Proposition15

  -- We can map the requests
  public export
  mapStarShp : (a =%> b) -> StarShp a -> StarShp b
  mapStarShp x Done = Done
  mapStarShp x (More p1) = More (MkEx (x.fwd p1.ex1) (\y : b.res (x.fwd p1.ex1) => assert_total $ mapStarShp x (p1.ex2 (x.bwd p1.ex1 y))))

  -- We can map the responses
  mapStarPos : (mor : a =%> b) -> (x : StarShp a) -> StarPos b (mapStarShp mor x) -> StarPos a x
  mapStarPos y Done z = MkUnit
  mapStarPos y (More (MkEx x1 x2)) (y1 ## y2) = y.bwd x1 y1 ## mapStarPos y (x2 (y.bwd x1 y1)) y2

  public export
  map_kleene : a =%> b -> Kleene a =%> Kleene b
  map_kleene mor = (mapStarShp mor) <! (mapStarPos mor)

  -- Mapping morphisms preserves identity
  public export 0
  kleene_pres_id : forall a. map_kleene (identity {a}) <%≡%> identity {a = Kleene a}
  kleene_pres_id = MkDepLensEq starShpMapId ?ddkleene_pres_id_rhs
    where
      starShpMapId : (x : StarShp a) -> mapStarShp (identity _) x === x
      starShpMapId Done = Refl
      starShpMapId (More (MkEx x1 x2)) = cong More
          $ cong2Dep MkEx Refl (funExtDep $ \vx => starShpMapId (x2 vx))

      kleene_pres_id_rhs :
          (vx : StarShp a) ->
          (vy : StarPos a (mapStarShp (identity _) vx)) -> let
             0 x1 : StarPos a (mapStarShp (Prelude.id <! (\_ => id)) vx)
             0 x2 : StarPos a vx
             x1 = vy
             x2 = mapStarPos (identity a) vx vy
             in ?a
--       kleene_pres_id_rhs Done () = Refl
--       kleene_pres_id_rhs (More x) (v1 ## v2) with (x.ex2 v1) proof p
--         kleene_pres_id_rhs (More (MkEx x1 x2)) (v1 ## ()) | Done = sigEqToEq $ MkSigEq Refl (rewrite p in IRefl ?)
--         kleene_pres_id_rhs (More (MkEx x1 x2)) (v1 ## v2) | More pat
--           = sigEqToEq $ MkSigEq Refl (kleene_pres_id_rhs (x2 v1) (rewrite p in v2))

{-
  -- Mapping morphisms preserves composition
  public export 0
  kleene_pres_comp : forall a, b, c. (f : a =%> b) -> (g : b =%> c) ->
                     map_kleene (f ⨾ g) <%≡%> (map_kleene f ⨾ map_kleene g)
  kleene_pres_comp f g = MkDepLensEq starShpComp eqBwd'
    where
      starShpComp : (vs : StarShp a) -> mapStarShp (f ⨾ g) vs = mapStarShp g (mapStarShp f vs)
      starShpComp Done = Refl
      starShpComp (More x) = cong More $
                             exEqToEq $
                             MkExEq Refl
                             (\vx => assert_total $ starShpComp (x .ex2 ((f ⨾ g) .bwd (x .ex1) vx)))

      eqBwd' : (v : StarShp a) -> (y : StarPos c (mapStarShp (f ⨾ g) v)) ->
          let 0 p1, p2 : StarPos a v
              p1 = mapStarPos (f ⨾ g) v y
              p2 = mapStarPos f v (mapStarPos g (mapStarShp f v) (replace {p = StarPos c} (starShpComp v) y))
          in p1 === p2
      eqBwd' Done y = Refl
      eqBwd' (More (MkEx x1 x2)) (y1 ## y2) = Calc $
        |~ mapStarPos (f ⨾ g) (More (MkEx x1 x2)) (y1 ## y2)
        ~~ (f ⨾ g).bwd x1 y1              ## mapStarPos (f ⨾ g) (x2 ((f ⨾ g).bwd x1 y1)) y2 ...(Refl)
        ~~ f.bwd x1 (g.bwd (f.fwd x1) y1) ## mapStarPos f (x2 (f.bwd x1 (g.bwd (f.fwd x1) y1))) (mapStarPos g (mapStarShp f (x2 (f.bwd x1 (g.bwd (f.fwd x1) y1)))) (replace {p = StarPos c} (starShpComp (x2 (f.bwd x1 (g.bwd (f.fwd x1) y1)))) y2))
            ...(sigEqToEq $ MkSigEq Refl ?adh)-- (eqBwd' (x2 (f .bwd x1 (g .bwd (f .fwd x1) y1))) y2))
        ~~ mapStarPos f (More (MkEx x1 x2)) (g.bwd (f.fwd x1) y1 ## mapStarPos g (mapStarShp f (x2 (f.bwd x1 (g.bwd (f.fwd x1) y1)))) (replace {p = StarPos c} (starShpComp (x2 (f.bwd x1 (g.bwd (f.fwd x1) y1)))) y2)) ...(Refl)
        ~~ mapStarPos f (More (MkEx x1 x2)) (mapStarPos g (More (MkEx (f.fwd x1)  (\y : b.res (f.fwd x1) => assert_total $ mapStarShp f (x2 (f.bwd x1 y))))) (replace {p = StarPos c} (starShpComp (More (MkEx x1 x2))) (y1 ## y2))) ...(Refl)
        ~~ mapStarPos f (More (MkEx x1 x2)) (mapStarPos g (mapStarShp f (More (MkEx x1 x2))) (replace {p = StarPos c} (starShpComp (More (MkEx x1 x2))) (y1 ## y2))) ...(Refl)

  partial
  KleeneFunctor : Functor Cont Cont
  KleeneFunctor = MkFunctor
      Kleene
      (\_, _ => map_kleene)
      (\_ => depLensEqToEq $ kleene_pres_id)
      (\a, b, c, f, g => depLensEqToEq $ kleene_pres_comp f g)

namespace StateCostateContext
  namespace Definition16

    public export
    State : Container -> Type
    State c = End =%> c

    public export
    value : State a -> a.req
    value m = m.fwd ()

    public export
    state : a.req -> State a
    state x = (const x) <! (\_, _ => ())

  namespace Definition17

    public export
    Costate : Container -> Type
    Costate c = c =%> End

    public export
    costate : ((x : a.req) -> a.res x) -> Costate a
    costate f = (const ()) <! (\x, _ => f x)

    public export
    exec : Costate a -> (x : a.req) -> a.res x
    exec m x = m.bwd x ()

  namespace Definition18

    Context : (a, b : Container) -> Type
    Context a b = a.req * ((x : b.req) -> b.res x)

    split : Context a b -> State a * Costate b
    split = bimap state costate

    run : (i : State a) -> Costate b -> a =%> b -> a.res (value i)
    run st co m = exec (m ⨾ co) (value st)

namespace Definition19

  Lift : (Type -> Type) -> Container -> Container
  Lift f c = (!>) c.req (f . c.res)

%unbound_implicits off
namespace Proposition20
  parameters (f : Functor Set Set)

    f_hom : {a, b : Container} -> a =%> b ->  Lift f.mapObj a =%> Lift f.mapObj b
    f_hom c = c.fwd <! (\x => f.mapHom _ _ (c.bwd x))

    public export 0
    f_pres_id : (a : Container) -> f_hom (identity {a}) <%≡%> identity {a = Lift f.mapObj a}
    f_pres_id a = MkDepLensEq (\_ => Refl) (\x, y => let hh = f.presId (a.res x) in app _ _ hh y)

    public export 0
    f_pres_comp : (a, b, c : Container) -> (f1 : a =%> b) -> (f2 : b =%> c) ->
                    f_hom (f1 ⨾ f2) <%≡%> f_hom f1 ⨾ f_hom f2
    f_pres_comp a b c f1 f2 = MkDepLensEq
        (\_ => Refl)
        (\v, y => let hh = f.presComp _ _ _ (f2.bwd ((f_hom f1).fwd v)) (f1.bwd v) in app _ _ hh y)

    LiftIsFunctor : Functor Cont Cont
    LiftIsFunctor = MkFunctor
      (Lift f.mapObj)
      (\_, _, m => f_hom m)
      (\x => depLensEqToEq $ f_pres_id x)
      (\a, b, c, f, g => depLensEqToEq $ f_pres_comp a b c f g)

namespace Proposition21
  parameters {mendo : Functor Set Set} (m : Monad' Set mendo)

    LiftFunctor' : Functor (Cont .op) (Cont .op)
    LiftFunctor' = MkFunctor
        (Lift mendo.mapObj)
        (\a, b => f_hom mendo)
        (\x => depLensEqToEq $ f_pres_id mendo x)
        (\a, b, c, f, g => depLensEqToEq $ f_pres_comp mendo c b a g f)

    base_counit : (v : Container) -> Lift mendo.mapObj v =%> v
    base_counit v = id <! (\x, y => m.unit.component (v.res x) y )

    base_comult : (v : Container) -> Lift mendo.mapObj v =%> Lift mendo.mapObj (Lift mendo.mapObj v)
    base_comult v = id <! (\x => m.mult.component (v.res x))

    identity_left : (v : Container) ->
                    base_comult v ⨾ base_counit (Lift mendo.mapObj v)
                    <%≡%>
                    identity {a = Lift mendo.mapObj v}
    identity_left v = MkDepLensEq (\_ => Refl) (\vx, y => let
                                  m' = m.identityLeft (v.res vx)
                                  in app _ _ m' y)

    identity_right : (v : Container) ->
                     base_comult v ⨾ f_hom mendo (base_counit v)
                     <%≡%>
                    identity {a = (Lift mendo.mapObj v)}
    identity_right v = MkDepLensEq (\_ => Refl) (\vx, vy => let
                                   m' = m.identityRight (v.res vx)
                                   in app _ _ m' vy)

    monad_square : (v : Container) ->
                   let Fn : Container -> Container
                       Fn = Lift mendo.mapObj
                       top : Fn v =%> Fn (Fn v)
                       top = base_comult v
                       right : Fn (Fn v) =%> Fn (Fn (Fn v))
                       right = f_hom mendo (base_comult v)
                       left : Fn v =%> Fn (Fn v)
                       left = base_comult v
                       bot : Fn (Fn v) =%> Fn (Fn (Fn v))
                       bot = base_comult (Fn v)
                    in top ⨾ right <%≡%> left ⨾ bot
    monad_square v = MkDepLensEq (\_ => Refl)
        (\vx, vy => app _ _ (m.square (v.res vx)) vy)

    comonad : ContainerComonad (LiftIsFunctor mendo)
    comonad = MkContainerComonad
        base_counit
        base_comult
        monad_square
        identity_left
        identity_right

%unbound_implicits on
namespace Definition22

  distrib_plus : Lift f (a + b) =%> Lift f a + Lift f b
  distrib_plus = id <! (\case (<+ x) => id ; (+> x) => id)

namespace Definition23

  distrib_maybeAll : Monad m => Lift m (All.Maybe a) =%> All.Maybe (Lift m a)
  distrib_maybeAll = id <! (\case Nothing => \x => pure Nay
                                ; (Just x) => \(Yay y) => map Yay y)

namespace Definition24

  seq2M : Monad m => Costate (Lift m a) -> Costate (Lift m b) -> Costate (Lift m (a >> b))
  seq2M x y = costate (\xn => do v1 <- runCostate x xn.π1
                                 v2 <- runCostate y (xn.π2 v1)
                                 pure (v1 ## v2))

