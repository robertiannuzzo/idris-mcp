module Data.CartMon

import Data.Container.Cartesian.Sequence.Monoidal

%logging 100
public export
alpha2 : F2 =>> F1
alpha2 = MkNT
    (\_ => Monoidal.alphaL)
    -----------------------------------------------
    -- Attempt 4
    -- (\xv, y, (m1 && (m2 && m3)) => cartEqToEq $ MkCartDepLensEq
    --     (\x => Refl)
    --     (\(MkEx (MkEx x1 x2) x3) => MkIsoEq
    --         (\(z1 ## (z2 ## z3)) => Refl)
    --         (\((z1 ## z2) ## z3) =>
    --             sigEqToEqS $ MkSigEqS Refl
    --             $ trans (sigEqToEq' $ MkSigEq' Refl ?que
    --                     )
    --                     (applyRefl' ? ?)
    -----------------------------------------------
    -- Attempt 3
    -- Changing the toplevel proof to include transport for morphisms makes the
    -- proof hard to compute and trying to evaluate away the substitution loops the compiler
    -- (\xv, y, (m1 && (m2 && m3)) => cartEqToEqTr $ MkCartDepLensEqTr
    --     (\x => Refl)
    --     (\(MkEx (MkEx x1 x2) x3) => MkIsoEq
    --         (\(v1 ## (v2 ## v3)) => trans ?thing (applyRefl ? ?))
    --         (?arra
    -----------------------------------------------
    -- attempt 2
    -- I think this is the most straightforward proof but the hole, despite its simplicity
    -- is impossible to fill without looping the compiler. its type is:
    -- (m3.cbwd (x3 (z1 ## z2))).from (transport (\x => ((xv .π2) .π2) .response (x3 x)) Refl z3) =
    -- (m3.cbwd (x3 (z1 ## z2))).from z3
    -- Which should be inhabited by the value `cong ((m3.cbwd (x3 (z1 ## z2))).from) (applyRefl ? ?)`
    -- but the compiler loops trying to typecheck it.
    (\xv, y, (m1 && (m2 && m3)) => cartEqToEq $ MkCartDepLensEq
        (\x => Refl)
        (\(MkEx (MkEx x1 x2) x3) => MkIsoEq
            (\(z1 ## (z2 ## z3)) => Refl)
            (\((z1 ## z2) ## z3) =>
                sigEqToEqS $ MkSigEqS Refl
                $ trans (sigEqToEqS $ MkSigEqS Refl
                        $ ((let rf := applyRefl (xv.π2.π2.response . x3) z3
                                rr : (m3 .cbwd (x3 (z1 ## z2))) .from (transport (\x => ((xv .π2) .π2) .response (x3 x)) Refl z3) === (m3 .cbwd (x3 (z1 ## z2))) .from z3 := fromEq (m3 .cbwd (x3 (z1 ## z2)))
                                            {x = transport (xv.π2.π2.response . x3) Refl z3, y = z3}
                                            rf
                            in rr) `trans`
                            (applyRefl' ? ?)) `trans`
                            (applyRefl' ? ?)
                        )
                        (applyRefl' ? ?)
    -------------------
    -- attempt1: the following proof should work but it loops the compiler
    -- (\xv, y, (m1 && (m2 && m3)) => cartEqToEq $ MkCartDepLensEq
    --     (\x => Refl)
    --     (\(MkEx (MkEx x1 x2) x3) => MkIsoEq
    --     (\((z1 ## z2) ## z3) => sigEqToEq' $ MkSigEq' Refl
    --          $ sigEqToEq' $ MkSigEq' Refl
    --          $ Calc $
    --          |~ (m3 .cbwd (x3 (z1 ## z2))).from (transport (\x => ((xv .π2) .π2) .response (x3 x)) Refl z3)
    --          ~~ (m3 .cbwd (x3 (z1 ## z2))).from z3
    --              ...(cong ((m3 .cbwd (x3 (z1 ## z2))) .from) (applyRefl' ? ?))
    --          ~~ transport (\x => ((y .π2) .π2) .response (m3 .cfwd (x3 ((m1 .cbwd x1) .to (x .π1) ## (m2 .cbwd (x2 ((m1 .cbwd x1) .to (x .π1)))) .to (x .π2))))) Refl ((m3 .cbwd (x3 (z1 ## z2))) .from z3)
    --              ...(applyRefl ? ?)
    -------------------
    -- attempt 5:
    -- Yep, still looping
    -- (\xv, y, (m1 && (m2 && m3)) => cartEqToEq $ MkCartDepLensEq
    --     (\x => Refl)
    --     (\(MkEx (MkEx x1 x2) x3) => MkIsoEq
    --         (\(z1 ## (z2 ## z3)) => Refl)
    --         (\((z1 ## z2) ## z3) =>
    --             ixSigToEq $ MkIxSigEq Refl $
    --             ixSigToEq $ MkIxSigEq Refl
    --               ?sahdui
            )
        )
    )
