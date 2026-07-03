module Data.Container.Maybe.Monoid

import Data.Category.Monoid
import Data.Category.Functor
import Data.Category.Bifunctor
import Data.Category.NaturalTransformation

import Data.Container
import Data.Container.Category
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.Cartesian.Sequence.Monoidal as Cart
import Data.Container.Cartesian.Sequence.Bifunctor
import Data.Container.Extension
import Data.Container.Maybe.Desc
import Data.Container.Tensor.Definition
import Data.Container.Tensor.Bifunctor
import Data.Container.Tensor.Monoidal
import Data.Container.Sequence.Monoidal
import Data.Container.Sequence.Bifunctor
import Data.Fin
import Data.Product
import Data.Coproduct
import Data.Iso

import Pipeline.Equality
public export
neutral : One =%> MaybeCont
neutral = const False <! (const absurd)

public export
mult : MaybeCont * MaybeCont =%> MaybeCont
mult = uncurry or <! (\case (True && x) => (<+)
                            (False && x) => (+>)
                      )
public export
MaybeMonoidOr : MonoidObject {o = Container} {cat = Cont} CartesianMonoidal
-- Proof in Appendix
MaybeMonoidOr = MkMonObj
    MaybeCont
    neutral
    mult
    (depLensEqToEq $ MkDepLensEq
        (\_ => Refl)
        (\_, _ => Refl)
    )
    (depLensEqToEq $ MkDepLensEq
        (\case (False && p2) => Refl
               (True && p2) => Refl)
        (\case (False && p2) => \x => absurd x
               (True && p2) => \_ => Refl)
    )
    (depLensEqToEq $ MkDepLensEq
        (\case ((False && b) && c) => Refl
               ((True && b) && c) => Refl)
        (\case ((False && False) && v3) => \xx => cong (+>) Refl
               ((False && True) && v3) => \xx => Refl
               ((True && v2) && v3) => \case xx => Refl
        )
    )
flat_rhs : Ex MaybeCont Bool -> Bool
flat_rhs (MkEx False ex2) = False -- return nothing if the outer maybe is Nothing
flat_rhs (MkEx True ex2) = ex2 TT -- return the inner maybe if the outer is Just

flat_rhs_lemma : (v : Bool) -> flat_rhs (MkEx v (\_ => True)) ≡ v
flat_rhs_lemma False = Refl
flat_rhs_lemma True = Refl

flat_bwd : (x : Ex MaybeCont Bool) -> IsTrue (flat_rhs x) ->
           Σ (IsTrue (x .ex1)) (\y => IsTrue (x .ex2 y))
flat_bwd (MkEx False ex2) y = absurd y
flat_bwd (MkEx True ex2) y = TT ## y

flat_bwd_lemma : (v : Bool) ->
   (w : IsTrue (flat_rhs (MkEx v (\_ => True)))) ->
   (rewrite flat_rhs_lemma v in π1 (flat_bwd (MkEx v (\_ => True)) w)) ≡ w
flat_bwd_lemma False w = absurd w
flat_bwd_lemma True TT = Refl

flat_bwd_lemma' : (v : Bool) ->
   (w : IsTrue (flat_rhs (MkEx v (\_ => True)))) ->
   (π1 (flat_bwd (MkEx v (\_ => True)) w)) ≡
   transport IsTrue (flat_rhs_lemma v) w
flat_bwd_lemma' False w = absurd w
flat_bwd_lemma' True TT = sym $ applyRefl IsTrue TT

public export
flat : MaybeCont ▷ MaybeCont =%> MaybeCont
flat = flat_rhs <! flat_bwd

public export
MaybeMonoidTensor : MonoidObject {o = Container, cat = Cont} TensorMonoidal
MaybeMonoidTensor = MkMonObj
  { obj = MaybeCont
  , η = fromUnit
  , mult = maybeMult
  , left = left
  , right = right
  , assoc = assoc
  }
  where
    fromUnit : I =%> MaybeCont
    fromUnit = const True <! const (const ())
    maybeMult : MaybeCont ⊗ MaybeCont =%> MaybeCont
    maybeMult = uncurry and <!
                \case (True && x) => \z => (TT && z)
                      (False && x) => absurd
    0 left : let 0 η_id_μ, λ : I ⊗ MaybeCont =%> MaybeCont
                 0 topMorphism : I ⊗ MaybeCont =%> MaybeCont ⊗ MaybeCont
                 topMorphism = fromUnit ~⊗~ identity MaybeCont
                 η_id_μ = topMorphism |%> maybeMult
                 λ = TensorMonoidal .leftUnitor.nat.component MaybeCont
              in η_id_μ === λ
    left = depLensEqToEq $ MkDepLensEq
             (\xx => Refl)
             (\xx, _ => Refl)
    0 right : let 0 id_η_μ, ρ : MaybeCont ⊗ I  =%> MaybeCont
                  0 topMorphism : MaybeCont ⊗ I  =%> MaybeCont ⊗ MaybeCont
                  topMorphism = identity MaybeCont ~⊗~ fromUnit
                  id_η_μ = topMorphism |%> maybeMult
                  ρ  = TensorMonoidal .rightUnitor.nat.component MaybeCont
               in id_η_μ === ρ
    right = depLensEqToEq $ MkDepLensEq
              (\xx => andR)
              (\case (True && xx) => \TT => Refl
                     (False && xx) => \yy => absurd yy)
    0 assoc : let
                  0 botLeft : (MaybeCont ⊗ MaybeCont) ⊗ MaybeCont =%> MaybeCont
                  botLeft = maybeMult ~⊗~ identity MaybeCont |%> maybeMult
                  0 assoc : ((MaybeCont ⊗ MaybeCont) ⊗ MaybeCont) =%> MaybeCont ⊗ (MaybeCont ⊗ MaybeCont)
                  assoc = TensorMonoidal .alpha.tan.component (MaybeCont && (MaybeCont && MaybeCont))
                  0 topRight : ((MaybeCont ⊗ MaybeCont) ⊗ MaybeCont) =%> MaybeCont
                  topRight = assoc |%> identity MaybeCont ~⊗~ maybeMult |%> maybeMult
              in botLeft === topRight
    assoc = depLensEqToEq $ MkDepLensEq
        (\x => andAssoc)
        (\case ((False && x2) && x3) => \y => absurd y
               ((True && False) && x3) => \y => absurd y
               ((True && True) && x3) => \y => Refl)
namespace Cont
  public export
  MaybeMonoidCompose : MonoidObject {o = Container} {cat = Cont} SequenceMonoidal
  -- Proof in Appendix
  MaybeMonoidCompose = MkMonObj
    MaybeCont
    ((\_ => True) <! (\_ => const ()))
    flat
    (depLensEqToEq $ MkDepLensEq (\v => Refl) (\_, _ => Refl))
    (depLensEqTrToEq $ MkDepLensEqTr
        (\v => flat_rhs_lemma v.ex1)
        (\e => \w => let
              fl = flat_bwd_lemma' _ w
            in sigEqToEq $ MkSigEq
                (fl)
                (IRefl fl)
        )
    )
    (depLensEqTrToEq $ MkDepLensEqTr
        assocFwd
        assocBwd)
  where
    0 assocFwd : (v : ((MaybeCont ▷ MaybeCont) ▷ MaybeCont).req) -> let
                 a, b : (MaybeCont ▷ MaybeCont) ▷ MaybeCont =%> MaybeCont
                 a = flat ~▷~ identity MaybeCont |%> flat
                 ass : (MaybeCont ▷ MaybeCont) ▷ MaybeCont =%>
                       MaybeCont ▷ (MaybeCont ▷ MaybeCont)
                 ass = Monoidal.assoc2 {a = MaybeCont, b = MaybeCont, c = MaybeCont}
                 b = ass
                      |%> (identity MaybeCont ~▷~ flat)
                          {a = MaybeCont, b = MaybeCont ▷ MaybeCont, b' = MaybeCont}
                      |%> flat
                 in a.fwd v === b.fwd v
    assocFwd (MkEx (MkEx False f) ex2) = Refl
    assocFwd (MkEx (MkEx True f) ex2) = Refl

    %unbound_implicits off

    0 assocBwd : (v : ((MaybeCont ▷ MaybeCont) ▷ MaybeCont).req) ->
                  let
                   dom : Container
                   dom = (MaybeCont ▷ MaybeCont) ▷ MaybeCont
                   0 p1 : dom.res v
                   a, b : dom =%> MaybeCont
                   a = flat ~▷~ identity MaybeCont |%> flat
                   ass : (MaybeCont ▷ MaybeCont) ▷ MaybeCont =%>
                         MaybeCont ▷ (MaybeCont ▷ MaybeCont)
                   ass = Monoidal.assoc2 {a = MaybeCont, b = MaybeCont, c = MaybeCont}
                   b = ass
                        |%> (identity MaybeCont ~▷~ flat)
                            {a = MaybeCont, b = MaybeCont ▷ MaybeCont, b' = MaybeCont}
                        |%> flat
                 in (y : MaybeCont .res (a.fwd v)) -> let
                   p1 = a.bwd v y
                   0 p2 : dom.res v
                   p2 = b.bwd v (transport MaybeCont .res (assocFwd v) y)
                 in  p1 === p2
    assocBwd (MkEx (MkEx False f) ex2) y = absurd y
    assocBwd (MkEx (MkEx True f) ex2) y = sigEqToEq $
        MkSigEq
            (sigEqToEq $ MkSigEq Refl (rewrite applyRefl IsTrue y in (IRefl Refl)))
            (rewrite applyRefl IsTrue y in IRefl Refl)
nothing : I =#> MaybeCont
nothing = MkCartDepLens (\_ => True) (\_ => MkIso (\_ => ()) (\_ => TT)
                        (\x => unitUniq x)
                        (\x => isTrueUniq x)
                        )

joinInhabited : Ex MaybeCont Bool -> Bool
joinInhabited (MkEx False ex2) = False
joinInhabited (MkEx True ex2) = ex2 TT

joinInhabitedBw :
  (m : Ex MaybeCont Bool) ->
  IsTrue (joinInhabited m)
  ≅ Σ (IsTrue m.ex1) (IsTrue . m.ex2)
joinInhabitedBw (MkEx False ex2) = IsoVoid
joinInhabitedBw (MkEx True ex2) = MkIso
    (\xx => TT ## xx)
    (\xx => transport (IsTrue . ex2) (sym (isTrueUniq xx.π1)) xx.π2 )
    (\xx => sigEqToEqS $ MkSigEqS (isTrueUniq xx.π1) Refl)
    (\xx => applyRefl ? ?)

join : MaybeCont ▷ MaybeCont =#> MaybeCont
join = MkCartDepLens
    joinInhabited
    joinInhabitedBw

joinInhabitedEx1 :
   (xx : Ex MaybeCont ()) ->
   joinInhabited (MkEx xx.ex1 (\x => True)) = xx.ex1
joinInhabitedEx1 (MkEx False x2) = Refl
joinInhabitedEx1 (MkEx True x2) = Refl

joinInhabitedCartBwd :
    (x : Ex MaybeCont ()) ->
    let
        0 topMorphism : MaybeCont ▷ I  =#> MaybeCont ▷ MaybeCont
        topMorphism = identity MaybeCont ~▷#~ Monoid.nothing
        0 a : MaybeCont ▷ I  =#> MaybeCont
        a = topMorphism |#> Monoid.join
        0 p1, p2 : MaybeCont .res (a.cfwd x) ≅ (MaybeCont ▷ I).res x
        p1 = a.cbwd x
        p2 = transport
                 (\arg => MaybeCont .res arg ≅ (MaybeCont ▷ I).res x)
                 ?hu
                 (Cart.unitR1.cbwd x)

    in IsoEq p1 p2
joinInhabitedCartBwd (MkEx False x2)
    = MkIsoEq (\x => ?uhu) (\x => absurd x.π1)
joinInhabitedCartBwd (MkEx True x2)
    = MkIsoEq (\xx => believe_me ())
        (\xx => believe_me ())

0
left : let 0 η_id_μ, λ : I ▷ MaybeCont =#> MaybeCont
           0 topMorphism : I ▷ MaybeCont =#> MaybeCont ▷ MaybeCont
           topMorphism = Monoid.nothing ~▷#~ identity MaybeCont
           η_id_μ = topMorphism |#> join
           λ = unitL1
        in η_id_μ === λ
left = cartEqToEq
    $ MkCartDepLensEq
      (\_ => believe_me ())
      (\xx => MkIsoEq
          (\_ => believe_me ())
          (\_ => believe_me ())
      )

0
right : let 0 id_η_μ, ρ : MaybeCont ▷ I  =#> MaybeCont
            0 topMorphism : MaybeCont ▷ I  =#> MaybeCont ▷ MaybeCont
            topMorphism = identity MaybeCont ~▷#~ Monoid.nothing
            id_η_μ = topMorphism |#> Monoid.join
            ρ  = Cart.unitR1 {a = MaybeCont}
         in id_η_μ `CartDepLensEqTr` ρ
-- right = MkCartDepLensEqTr
--   joinInhabitedEx1
--   joinInhabitedCartBwd

0
botLeft : (MaybeCont ▷ MaybeCont) ▷ MaybeCont =#> MaybeCont
botLeft = Monoid.join ~▷#~ identity MaybeCont |#> Monoid.join
0
topRight : ((MaybeCont ▷ MaybeCont) ▷ MaybeCont) =#> MaybeCont
topRight = Monoidal.alphaL {a = MaybeCont, b = MaybeCont, c = MaybeCont}
    |#> identity MaybeCont ~▷#~ Monoid.join |#> Monoid.join

0
assocFwdEq :
    (x : ((MaybeCont ▷ MaybeCont) ▷ MaybeCont).req) ->
    botLeft.cfwd x === topRight.cfwd x
-- assocFwdEq (MkEx (MkEx False ex2) ex3) = Refl
-- assocFwdEq (MkEx (MkEx True ex2) ex3) with (ex2 TT)
--   assocFwdEq (MkEx (MkEx True ex2) ex3) | False = Refl
--   assocFwdEq (MkEx (MkEx True ex2) ex3) | True = Refl

assocBwdEq :
    (x : ((MaybeCont ▷ MaybeCont) ▷ MaybeCont).req) ->
    let 0 p1 : MaybeCont .res (botLeft.cfwd x) ≅ ((MaybeCont ▷ MaybeCont) ▷ MaybeCont).res x
        p1 = botLeft.cbwd x
        0 p2 : MaybeCont .res (botLeft.cfwd x) ≅ ((MaybeCont ▷ MaybeCont) ▷ MaybeCont).res x
        p2 = transport (\arg => MaybeCont .res arg ≅ ((MaybeCont ▷ MaybeCont) ▷ MaybeCont).res x) (sym $ assocFwdEq x) (topRight.cbwd x)
    in IsoEq p1 p2
assocBwdEq aa = ?oo
-- assocBwdEq (MkEx (MkEx False ex2) ex3)
--   = MkIsoEq (\x => believe_me x) (\x => absurd x.π1.π1)
-- assocBwdEq (MkEx (MkEx True ex2) ex3) with (ex2 TT) proof pt
--   assocBwdEq (MkEx (MkEx True ex2) ex3) | False
--     = MkIsoEq (\x => believe_me x)
--     (\((TT ## x1) ## x2) => absurd (replace {p = IsTrue} pt x1))
--   assocBwdEq (MkEx (MkEx True ex2) ex3) | True with (ex3 (TT ## (replace {p = IsTrue} (sym pt) TT))) proof qt
--     assocBwdEq (MkEx (MkEx True ex2) ex3) | True | False
--       = MkIsoEq (\x => believe_me x)
--           (\((TT ## x1) ## x2) => believe_me ())
--     assocBwdEq (MkEx (MkEx True ex2) ex3) | True | True
--       = MkIsoEq (\xx => believe_me ())(\xx => believe_me ())

0
assoc : Monoid.botLeft `CartDepLensEqTr` Monoid.topRight
assoc = MkCartDepLensEqTr
    assocFwdEq
    assocBwdEq

namespace Cart
    public export
    MaybeMonoidCompose : MonoidObject {o = Container} {cat = ContCart} SequenceMonoidal
    MaybeMonoidCompose = MkMonObj
        MaybeCont
        nothing
        join
        left
        (cartEqToEqTr right)
        (believe_me ()) --(cartEqToEqTr assoc)
