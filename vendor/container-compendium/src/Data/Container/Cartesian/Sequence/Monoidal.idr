module Data.Container.Cartesian.Sequence.Monoidal

import Data.Category.Monoid
import Data.Category.Bifunctor
import Data.Category.Endofunctor
import Data.Category.NaturalTransformation

import Data.Container
import Data.Container.Extension
import Data.Container.Sequence.Definition
import Data.Container.Category
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.Cartesian.Sequence.Bifunctor

import Data.Iso
import Proofs.Transport

import Pipeline.Equality
import Syntax.PreorderReasoning


public export
alphaL : (a ▷ b) ▷ c =#> a ▷ (b ▷ c)
alphaL = (\x => MkEx x.ex1.ex1 (\v => MkEx (x.ex1.ex2 v) (\w => x.ex2 (v ## w))))
    <#! (\x => MkIso (\y => (y.π1 ## y.π2.π1) ## y.π2.π2)
                     (\y => y.π1.π1 ## (y.π1.π2 ## transport (c.response . x.ex2) (sym $ sigmaProjId y.π1) y.π2 ))
                     (\xx => sigEqToEqS $ MkSigEqS (sigmaProjId xx.π1) Refl)
                     (\xx => sigEqToEqS $ MkSigEqS Refl
                       (sigEqToEqS $ MkSigEqS
                         (cong Σ.π1 (applyRefl' ? xx.π2))
                         (believe_me ())
                         -- (Calc $
                         --   |~ transport (c.response . x.ex2) Refl xx.π2.π2
                         --   ~~ xx.π2.π2
                         --       ...(applyRefl (c.response . x.ex2) xx.π2.π2)
                         --   ~~ rewrite__impl
                         --          (\y => c .response (x .ex2 (xx.π1 ## y)))
                         --          ?
                         --          (xx.π2.π2)
                         --       ...(Refl)
                         --   ~~ transport
                         --          (\y => c .response (x .ex2 (xx.π1 ## y)))
                         --          (sym (cong π1 (applyRefl' (\y => Σ (b .response (x.ex1.ex2 y)) (\z => c.response (x.ex2 (y ## z)))) xx.π2)))
                         --          ((xx.π2) .π2)
                         --       ...(?dudu)
                         --   ~~ transport
                         --          (\y => c .response (x .ex2 (xx.π1 ## y)))
                         --          (sym (cong π1 (applyRefl' (\y => Σ (b .response (x.ex1.ex2 y)) (\z => c.response (x.ex2 (y ## z)))) xx.π2)))
                         --          ((transport (\y => Σ (b .response ((x .ex1) .ex2 y)) (\z => c .response (x .ex2 (y ## z)))) Refl (xx .π2)) .π2)
                         --       ...(?aio)
                         -- )
                       )
                     )
        )

-- m3 .cfwd (ax .ex2 ((m1 .cbwd ((ax .ex1) .ex1)) .to xx ## (m2 .cbwd ((ax .ex1) .ex2 ((m1 .cbwd ((ax .ex1) .ex1)) .to xx))) .to yy))
-- m3 .cfwd (ax .ex2 ((mapBackward a a' b b' m1 m2 (ax .ex1)) .to (transport (a' .response) Refl xx ## transport (b' .response) (congDep (\ggq => m2 .cfwd ((ax .ex1) .ex2 ((m1 .cbwd ((ax .ex1) .ex1)) .to ggq))) (applyRefl' (a' .response) xx)) yy)))

0
alphaL_Natural : {0 a, a', b, b', c, c' : Container} ->
  (m1 : a =#> a') ->
  (m2 : b =#> b') ->
  (m3 : c =#> c') ->
  let 0 Func1 : a ▷ (b ▷ c) =#> a' ▷ (b' ▷ c')
      Func1 = (m1 ~▷#~ (m2 ~▷#~ m3) {a = b, a' = b', b = c, b' = c'})
                  {a, a', b = b ▷ c, b' = b' ▷ c'}
      0 F1, F2 : (a ▷ b) ▷ c =#> a' ▷ (b' ▷ c')
      F1 = alphaL {a, b, c} |#> Func1
      F2 = (m1 ~▷#~ m2) ~▷#~ m3 |#> alphaL {a = a', b = b', c= c'}
  in F1 === F2
alphaL_Natural m1 m2 m3 = cartEqToEqTr $ MkCartDepLensEqTr
    (\ax => believe_me ()) --(\xx => exEqToEq $ MkExEq
             -- (congDep (\ggq => m2.cfwd ((ax.ex1).ex2 ((m1 .cbwd (ax.ex1.ex1)).to ggq))) (applyRefl' a'.response xx))
             -- (\yy => cong (m3.cfwd . ax.ex2) (sigEqToEqS $ MkSigEqS ?oqiw ?bbbc))))
    (\ax => MkIsoEq
        (\y => believe_me ())
        (\y => believe_me ()
        )
    )

public export
alphaR : a ▷ (b ▷ c) =#> (a ▷ b) ▷ c
alphaR = (\x => MkEx (MkEx x.ex1 (\v => ex1 (x.ex2 v))) (\v => (x.ex2 v.π1).ex2 v.π2))
    <#! (\x => MkIso
            (\y => y.π1.π1 ## (y.π1.π2 ## y.π2))
            (\y => (y.π1 ## y.π2.π1) ## y.π2.π2)
            (\_ => sigEqToEq' $ MkSigEq' Refl (sigmaProjId _))
            (\_ => sigEqToEq' $ MkSigEq' (sigmaProjId _) Refl)
        )

public export
unitL1 : I ▷ a =#> a
unitL1 = (\x => x.ex2 ()) <#!
         (\x => MkIso
             (\y => () ## y)
             (\y => transport (a.response . x.ex2) (sym $ unitUniq y.π1) y.π2)
             (\_ => sigEqToEqS $ MkSigEqS (unitUniq _) Refl)
             (\x => applyRefl ? ?)
          )

public export
unitL2 : a =#> I ▷ a
unitL2 = (\x => MkEx () (\_ => x)) <#!
         (\x => MkIso
             (\x => x.π2)
             (() ##)
             (\_ => Refl)
             (\x => sigEqToEq $ MkSigEq (unitUniq _) (IRefl (unitUniq _))))


public export
unitR1 : a ▷ I =#> a
unitR1 = (\x => x.ex1) <#!
         (\x => MkIso
           (## ())
           (\y => y.π1)
           (\y => sigEqToEqS $ MkSigEqS Refl (trans (unitUniq y.π2) (applyRefl' ? ?)))
           (\_ => Refl)
         )

public export
unitR2 : a =#> a ▷ I
unitR2 = (\x => MkEx x (\_ => ())) <#!
         (\x => MkIso
             (\y => y.π1)
             (##())
             (\_ => Refl)
             (\y => sigEqToEqS $ MkSigEqS Refl (trans (unitUniq y.π2) (applyRefl' ? ?)))
          )

-- ((m .π1 ~▷#~ (m .π2) .π1) ~▷#~ (m .π2) .π2).cfwd
--   (MkEx (MkEx (_ .ex1) (\v => (_ .ex2 v) .ex1)) (\v => (_ .ex2 (v .π1)) .ex2 (v .π2)))
--
-- MkEx (MkEx (((m .π1 ~▷#~ ((m .π2) .π1 ~▷#~ (m .π2) .π2)) .cfwd _) .ex1) (\v => (((m .π1 ~▷#~ ((m .π2) .π1 ~▷#~ (m .π2) .π2)) .cfwd _) .ex2 v) .ex1)) (\v =>
-- (((m .π1 ~▷#~ ((m .π2) .π1 ~▷#~ (m .π2) .π2)) .cfwd _) .ex2 (v .π1)) .ex2 (v .π2))

%unbound_implicits off
export
F1, F2 : (ContCart × (ContCart × ContCart)) ->> ContCart
F1 = ((idF ContCart) `pair` SequenceBifunctor) ⨾⨾ SequenceBifunctor
F2 = Bifunctor.assocR {a = ContCart, b = ContCart, c = ContCart} ⨾⨾ ((SequenceBifunctor `pair` idF ContCart) ⨾⨾ SequenceBifunctor)

public export
alpha1 : F1 =>> F2
alpha1 = MkNT
    (\_ => Monoidal.alphaR)
    (\x, y, m => cartEqToEq $ MkCartDepLensEq
        (\z => believe_me ())
        (\xv => MkIsoEq
            (\y => believe_me ())
            (\_ => believe_me ())
        )
    )


alpha2 : F2 =>> F1
alpha2 = MkNT
    (\_ => alphaL)
    (\x, y, m => cartEqToEq $ MkCartDepLensEq
        (\z => believe_me ())
        (\xv => MkIsoEq
            (\y => believe_me ())
            (\_ => believe_me ())
        )
    )

public export
alpha : F1 =~= F2
alpha = MkNaturalIsomorphism
    alpha1
    alpha2
    ?aa
    ?bb
-- alpha = MkNaturalIsomorphism
--     alpha1
--     alpha2
--     (\(c1 && (c2 && c3)) => cartEqToEq $ MkCartDepLensEq
--       (\(MkEx x1 x2) => exEqToEqRw $ MkExEqRw Refl (\x3 => exEqToEqRw $ MkExEqRw Refl (\_ => Refl)))
--       (\(MkEx x1 x2) => MkIsoEq
--           (\(y1 ## (y2 ## y3)) => Refl)
--           (\(y1 ## (y2 ## y3)) => cong (y1 ##) $
--                                   sigEqToEq $ MkSigEq Refl $
--                                   eqToIxEq (applyRefl ? y3)
--           )
--       )
--     )
--     (\(c1 && (c2 && c3)) => cartEqToEq $ MkCartDepLensEq
--       (\(MkEx x1 x2) => exEqToEqRw $ MkExEqRw
--           (exEqToEqRw $ MkExEqRw Refl (\_ => Refl))
--           (\v => cong x2 $ sigEqToEq $ MkSigEq Refl (IRefl Refl)))
--       (\(MkEx x1 x2) => MkIsoEq
--         (\((y1 ## y2) ## y3) => sigEqToEq $ MkSigEq
--             Refl
--             (IRefl Refl))
--         (\((y1 ## y2) ## y3) => sigEqToEq $ MkSigEq
--             Refl
--             (eqToIxEq $ applyRefl (c3.response . x2) y3)
--         )
--       )
--     )

0 LeftUnit : Endo ContCart
LeftUnit = applyL {a = ContCart, b = ContCart, c = ContCart} I SequenceBifunctor

public export
leftUnitor1 : LeftUnit =>> idF ContCart
leftUnitor1 = MkNT
    (\_ => unitL1)
    (\x, y, m => cartEqToEq $ MkCartDepLensEq
        (\_ => believe_me ())
        (\z => MkIsoEq
          (\_ => ?leftUnitor30)
          (\z => ?leftUnitor31)
        )
    )

public export
leftUnitor2 : idF ContCart =>> LeftUnit
leftUnitor2 = MkNT
    (\_ => unitL2)
    (\x, y, m => cartEqToEq $ MkCartDepLensEq
        (\_ => believe_me ())
        (\z => MkIsoEq
            (\_ => ?leftUNitor28)
            (\_ => ?leftUnitor29)
        )
    )

public export
leftUnitor : LeftUnit =~= idF ContCart
leftUnitor = MkNaturalIsomorphism
    leftUnitor1
    leftUnitor2
    (\_ => cartEqToEq $ MkCartDepLensEq
        (\e => exEqToEqRw $ MkExEqRw (unitUniq e.ex1) (\v => cong e.ex2 (unitUniq v)))
        (\x => MkIsoEq
            (\y => sigEqToEq $ MkSigEq (unitUniq _) (IRefl (unitUniq y.π1)))
            (\y =>  (believe_me ()))
        )
    )
    (\z => believe_me ()
    )

0 RightUnit : Endo ContCart
RightUnit = applyR {a = ContCart, b = ContCart, c = ContCart} I SequenceBifunctor

public export
rightUnitor1 : RightUnit =>> idF ContCart
rightUnitor1 = MkNT
   (\_ => unitR1)
   (\x, y, m => cartEqToEq $ MkCartDepLensEq
       (\w => ?arg)
       (\w => MkIsoEq
         (\z => ?unitorRIghtRefl)
         (\z => ?unitorRIghtRefl2)
       )
   )

public export
rightUnitor2 :
    let 0 rightAppliedMult : Endo ContCart
        rightAppliedMult = applyR {a = ContCart, b = ContCart, c = ContCart} I SequenceBifunctor
    in idF ContCart =>>rightAppliedMult
rightUnitor2 = MkNT
    (\_ => unitR2)
    (\x, y, m => cartEqToEq $ MkCartDepLensEq
        (\_ => believe_me ())
        (\z => MkIsoEq
            (\_ => ?rightUnitor4)
            (\_ => ?rightUnitor3)
        )
    )

public export
rightUnitor :
    let 0 rightAppliedMult : Endo ContCart
        rightAppliedMult = applyR {a = ContCart, b = ContCart, c = ContCart} I SequenceBifunctor
    in rightAppliedMult =~= idF ContCart
rightUnitor = MkNaturalIsomorphism
  rightUnitor1
  rightUnitor2
  (\x => cartEqToEq $ MkCartDepLensEq
      (\y => exEqToEqRw $ MkExEqRw Refl (\v => unitUniq (y.ex2 v)))
      (\y => MkIsoEq
        (\z => sigEqToEq $ MkSigEq Refl (eqToIxEq (unitUniq z.π2)))
        (\(z) => sigEqToEq $ MkSigEq Refl (eqToIxEq (unitUniq z.π2)))
      )
  )
  (\x => cartEqToEq $ MkCartDepLensEq
    (\_ => Refl)
    (\z => MkIsoEq
      (\_ => ?rightUnitor23)
      (\_ => ?rightUnitor22)
    )
  )




namespace Cart
  -- ContCart is monoidal on ▷
  public export
  SequenceMonoidal : Monoidal ContCart
  SequenceMonoidal = MkMonoidal
      Cart.SequenceBifunctor
      I
      alpha
      leftUnitor
      rightUnitor

