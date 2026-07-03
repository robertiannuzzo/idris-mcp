module Data.Container.Lift

import Data.Container.Apply.Definition
import Data.Container.Definition
import Data.Container.Monad
import Data.Container.Category
import Data.Container.Closed
import Data.Container.Morphism
import Data.Container.Morphism.Eq
import Data.Container.Sequence.Bifunctor

import Data.Category
import Data.Category.Functor
import Data.Category.Bifunctor
import Data.Category.Functor.Category
import Data.Category.Endofunctor
import Data.Category.Monad
import Data.Category.NaturalTransformation

import Syntax.PreorderReasoning

%hide Prelude.Ops.infixl.(|>)
FApplyBifunctor : Bifunctor (EndoCat Set).op Cont Cont
FApplyBifunctor = MkFunctor
    { mapObj = (\f => f.π1.mapObj • f.π2)
    , mapHom = mapHom
    , presId = presId
    , presComp = presComp
    } -- proofs in appendix
    where
      mapHom : (x, y : Endo Set * Container) ->
               (y.π1 =>> x.π1) * (x.π2 =%> y.π2) ->
               x.π1.mapObj • x.π2 =%> y.π1.mapObj • y.π2
      mapHom x y (nt && mor) = mor.fwd <! \z, w =>
                               let fy : (y .π1) .mapObj ((x .π2) .response z)
                                 ; fy = y.π1.mapHom ? ? (mor.bwd z) w
                                in nt.component (x.π2.res z) fy
      0 presId : (v : Endo Set * Container) ->
               mapHom v v (((EndoCat Set) .op × Cont).id v)
               === Cont .id (v.π1.mapObj • v.π2)
      presId ((MkFunctor mo mh pid pcp) && p2) = depLensEqToEq $ MkDepLensEq
          (\_ => Refl)
          (\v, z => let 0 prf = app (pid (p2 .response v)) z
              in trans (cong (mh (p2 .response v) (p2 .response v) id) prf) prf)
      0 presComp :
        (x, y, z : Endo Set * Container) -> -- given three objects x, y, z
        (f : (y.π1 =>> x.π1) * (x.π2 =%> y.π2)) ->   -- a morphism x -> y
        (g : (z.π1 =>> y.π1) * (y.π2 =%> z.π2)) ->   -- and a morphism y -> z

        let 0 f1, f2 : (x.π1.mapObj • x.π2) =%> (z.π1.mapObj • z.π2)
            -- Mapping the morphism after composition
            f1 = mapHom x z (g.π1 ⨾⨾⨾ f.π1 && (f.π2 |%> g.π2))
            -- -- And composing the maps of each morphism
            f2 = mapHom x y f |%> mapHom y z g
        in f1 === f2 -- Are the same thing
      presComp (x1 && x2) (y1 && y2) (z1 && z2) (f1 && f2) (g1 && g2) = depLensEqToEq $ MkDepLensEq
          (\w => Refl)
          (\xv, yv => cong (f1.component (x2.response xv)) $ let
            cc = app (sym $ g1.commutes (z2 .response (g2 .fwd (f2 .fwd xv))) (x2.response xv) (\x => f2.bwd xv (g2.bwd (f2.fwd xv) x))) yv
            cc2 = app (g1.commutes (z2 .response (g2 .fwd (f2 .fwd xv))) (y2 .response (f2 .fwd xv)) (g2 .bwd (f2 .fwd xv))) yv
            cp = y1.presComp ? ? ? (g2.bwd (f2.fwd xv)) (f2.bwd xv)
            in Calc $
            |~ g1.component (x2.response xv) (z1.mapHom (z2.response (g2.fwd (f2.fwd xv))) (x2.response xv) (\x => f2.bwd xv (g2.bwd (f2.fwd xv) x)) yv)
            ~~ y1.mapHom ? ? ((f2.bwd xv) . (g2.bwd (f2.fwd xv))) (g1.component (z2.response (g2.fwd (f2.fwd xv))) yv)
                ...(cc)
            ~~ y1.mapHom ? ? (f2.bwd xv) (y1.mapHom ? ? (g2.bwd (f2.fwd xv)) (g1.component (z2.response (g2.fwd (f2.fwd xv))) yv))
                ...(app cp (g1.component (z2.response (g2.fwd (f2.fwd xv))) yv))
            ~= y1.mapHom ? ? (f2.bwd xv) (y1.mapHom (z2.response (g2.fwd (f2.fwd xv))) (y2.response (f2.fwd xv)) (g2.bwd (f2.fwd xv)) (g1.component (z2.response (g2.fwd (f2.fwd xv))) yv))
            ~~ y1.mapHom ? ? (f2.bwd xv) (g1.component (y2.response (f2.fwd xv)) (z1.mapHom ? ? (g2.bwd (f2.fwd xv)) yv))
                ...(cong (y1.mapHom ? ? (f2.bwd xv)) cc2)
            ~= y1.mapHom (y2.response (f2.fwd xv)) (x2.response xv) (f2.bwd xv) (g1.component (y2.response (f2.fwd xv)) (z1.mapHom (z2.response (g2.fwd (f2.fwd xv))) (y2.response (f2.fwd xv)) (g2.bwd (f2.fwd xv)) yv))
          )
parameters (f : Endo Set)
  FApplyFunctor : Endo Cont
  FApplyFunctor = applyBifunctor {a = (EndoCat Set).op} f FApplyBifunctor
ContComonad : (Monad Set e) -> Comonad Cont (FApplyFunctor e)
NTmapFst : {a, b, c, d : Category _} -> (f : a ->> b) -> {g, h : c ->> d} -> g =>> h -> (f `pair` g) =>> (f `pair` h)
NTmapFst fn nt = MkNT
    (\v => b.id (((pair fn h) .mapObj v) .π1) && nt.component v.π2)
    (\(x1 && x2), (y1 && y2), (m1 && m2) => ?NTmapFst_rhs)

idFCombine : {a, b : Category _} -> (idF a `pair` idF b) =>> idF (a × b)
idFCombine = MkNT (\v => a.id _ && b.id _) (\x, y, m => cong2 (&&) ?ahd ?idFCombine_rhs)

parameters {endo : Endo Set}

  %unbound_implicits off
  private
  m : Type -> Type
  m = endo.mapObj

  M : Endo Cont
  M = FApplyFunctor endo

  parameters {mon : Monad Set endo}

    -- extract the monads nexted in the second projection
    stren : {a : Type} -> {b : a -> Type} ->
              (Σ (x : a) | m (b x)) ->
              m (Σ (x : a) | (b x))
    stren p = endo.mapHom ? ? (p.π1 ##) p.π2

    -- same as above but nested in an extra level of monad
    joinSnd : {a : Type} -> {b : a -> Type} ->
              m (Σ (x : a) | m (b x)) ->
              m (Σ (x : a) | b x)
    joinSnd x = let join : ?
                    join = mon.mult.component (Σ a b)
                in join (endo.mapHom ? ? stren x)


    com : Comonad Cont M
    com = ContComonad mon

    -- m • (a ▷ b)
    mab : (Cont × Cont) ->> Cont
    mab = SequenceBifunctor ⨾⨾ M

    -- this is to make some proofs a bit easier
    -- m • (a ▷ b)
    mab' : (Cont × Cont) ->> Cont
    mab' = idF (Cont × Cont) ⨾⨾ mab

    -- m • (a ▷ m • b)
    mamb : (Cont × Cont) ->> Cont
    mamb = (idF Cont `Bifunctor.pair` M) ⨾⨾ mab


    ExtractN : M =>> idF Cont
    ExtractN = com.extract

    extractNID : (idF Cont `pair` M) =>> (idF Cont `pair` idF Cont)
    extractNID = NTmapFst (idF Cont) ExtractN

    ExtractNID' : (idF Cont `pair` M) =>> idF (Cont × Cont)
    ExtractNID' = extractNID ⨾⨾⨾ idFCombine {a = Cont, b = Cont}

    δNat : mamb =>> mab'
    δNat = (ExtractNID' -⨾ mab) {c = Cont × Cont, d = Cont}
    δ : {a, b : _} -> m • (a ▷ b) =%> m • (a ▷ m • b)
    δ = id <! (\x, y => joinSnd {a = a.response x.ex1, b = b.response . x.ex2 } y )
%unbound_implicits on
export
counit : (0 m : Type -> Type) -> Monad m => m • a =%> a
counit _ = id <! \_ => pure

export
cojoin : (0 m : Type -> Type) -> Monad m => m • a =%> m • m • a
cojoin m = id <! \_ => join
namespace Monad
  export
  δ : Monad m => {a, b : _} -> m • (a ▷ b) =%> m • (a ▷ m • b)
  δ = id <! (\x, y => do (y1 ## y2) <- y ; pure (y1 ## !y2))

  export
  distribTensor : Monad m => {0 a, b : Container} -> m • (a ⊗ b) =%> (m • a) ⊗ (m • b)
  distribTensor = id <! (\x, y => pure $ !y.π1 && !y.π2 )

  export
  fmap : Functor m => a =%> b -> m • a =%> m • b
  fmap lens = lens.fwd <! (\x => map (lens.bwd x))
