module Data.Container.Sequence.Monoidal

import public Data.Category.Bifunctor
import public Data.Category.Endofunctor
import public Data.Category.Functor
import public Data.Category.Monoid
import public Data.Category.NaturalTransformation
import public Data.Category.Product

import public Data.Container
import public Data.Container.Category
import public Data.Container.Sequence.Definition
import public Data.Container.Sequence.Bifunctor
import public Proofs.Extensionality
----------------------------------------------------------------------------------
-- Associator
----------------------------------------------------------------------------------
public export
assoc1 : a ▷ (b ▷ c) =%> (a ▷ b) ▷ c
assoc1 = (\x => MkEx (MkEx x.ex1 (\v => ex1 (x.ex2 v))) (\v => (x.ex2 v.π1).ex2 v.π2))
      <! (\x, y => y.π1.π1 ## y.π1.π2 ## y.π2)

public export
assoc2 : (a ▷ b) ▷ c =%> a ▷ (b ▷ c)
assoc2 = (\x => MkEx x.ex1.ex1 (\v => MkEx (x.ex1.ex2 v) (\w => x.ex2 (v ## w))))
      <! (\x, y => (y.π1 ## y.π2.π1) ## y.π2.π2)

public export
alpha1 : let f1, f2 : (Cont × (Cont × Cont)) ->> Cont
             f1 = ((idF Cont) `pair` SequenceBifunctor) ⨾⨾ SequenceBifunctor
             f2 = assocR {a = Cont, b = Cont, c = Cont} ⨾⨾ ((SequenceBifunctor `pair` idF Cont) ⨾⨾ SequenceBifunctor)
         in f1 =>> f2
alpha1 = MkNT
    (\_ => assoc1)
    (\x, y, m => depLensEqToEq $ MkDepLensEq
        (\w => Refl)
        (\w, z => sigEqToEq $ MkSigEq Refl (IRefl {prf = Refl}))
    )

public export
alpha2 : let f1, f2 : (Cont × (Cont × Cont)) ->> Cont
             f1 = ((idF Cont) `pair` SequenceBifunctor) ⨾⨾ SequenceBifunctor
             f2 = assocR {a = Cont, b = Cont, c = Cont} ⨾⨾ ((SequenceBifunctor `pair` idF Cont) ⨾⨾ SequenceBifunctor)
         in f2 =>> f1
alpha2 = MkNT
    (\_ => assoc2)
    (\x, y, m => depLensEqToEq $ MkDepLensEq
        (\w => Refl)
        (\w, z => Refl)
    )

public export
alpha : let f1, f2 : (Cont × (Cont × Cont)) ->> Cont
            f1 = ((idF Cont) `pair` SequenceBifunctor) ⨾⨾ SequenceBifunctor
            f2 = assocR {a = Cont, b = Cont, c = Cont} ⨾⨾ ((SequenceBifunctor `pair` idF Cont) ⨾⨾ SequenceBifunctor)
        in f1 =~= f2
alpha = MkNaturalIsomorphism
    alpha1
    alpha2
    (\v => depLensEqToEq $ MkDepLensEq
        (\e => exEqToEqRw $ MkExEqRw Refl (\q => exUniq (e.ex2 q)))
        (\q, p => sigEqToEq' $ MkSigEq' Refl (sigmaProjId _))
    )
    (\vq => depLensEqToEq $ MkDepLensEq
        (\w => exEqToEqRw $ MkExEqRw (exUniq w.ex1) (\vx => cong w.ex2 (sigmaProjId vx)))
        (\w, z => sigEqToEq $ MkSigEq (sigmaProjId _) (IRefl {prf = sigmaProjId _})
        )
    )
----------------------------------------------------------------------------------
-- Left Unitor
----------------------------------------------------------------------------------
public export
unitL1 : I ▷ a =%> a
unitL1 = (\x => x.ex2 ()) <! (\x, y => () ## y)

public export
unitL2 : a =%> I ▷ a
unitL2 = (\x => MkEx () (const x)) <! (\x, y => y.π2)

public export
leftUnitor1 :
    let 0 leftAppliedMult : Endo Cont
        leftAppliedMult = applyL {a = Cont, b = Cont, c = Cont} I SequenceBifunctor
    in leftAppliedMult =>> idF Cont
leftUnitor1 = MkNT
    (\_ => unitL1)
    (\x, y, m => Refl)

public export
leftUnitor2 :
    let 0 leftAppliedMult : Endo Cont
        leftAppliedMult = applyL {a = Cont, b = Cont, c = Cont} I SequenceBifunctor
    in idF Cont =>> leftAppliedMult
leftUnitor2 = MkNT
    (\_ => unitL2)
    (\x, y, m => Refl)

-- apply unit to the left
public export
leftUnitor :
    let 0 leftAppliedMult : Endo Cont
        leftAppliedMult = applyL {a = Cont, b = Cont, c = Cont} I SequenceBifunctor
    in leftAppliedMult =~= idF Cont
leftUnitor = MkNaturalIsomorphism
    leftUnitor1
    leftUnitor2
    (\v => depLensEqToEq $ MkDepLensEq
        (\q => exEqToEqRw $ MkExEqRw (unitUniq _) (\() => Refl))
        (\q, z => sigEqToEq $ MkSigEq (unitUniq _) (IRefl (unitUniq _))))
    (\v => Refl)

----------------------------------------------------------------------------------
-- Right Unitor
----------------------------------------------------------------------------------

public export
unitR1 : a ▷ I  =%> a
unitR1 = ex1 <! (\x, y => y ## ())

public export
unitR2 : a =%> a ▷ I
unitR2 = (\x => MkEx x (\_ => ())) <! (\x, y => y.π1)

public export
rightUnitor1 :
    let 0 rightAppliedMult : Endo Cont
        rightAppliedMult = applyR {a = Cont, b = Cont} I SequenceBifunctor
    in rightAppliedMult =>> idF Cont
rightUnitor1 = MkNT
    (\_ => unitR1)
    (\x, y, m => Refl)


public export
rightUnitor2 :
    let 0 rightAppliedMult : Endo Cont
        rightAppliedMult = applyR {a = Cont, b = Cont} I SequenceBifunctor
    in idF Cont =>> rightAppliedMult
rightUnitor2 = MkNT
    (\_ => unitR2)
    (\x, y, m => Refl)

public export
rightUnitor :
    let 0 rightAppliedMult : Endo Cont
        rightAppliedMult = applyR {a = Cont, b = Cont} I SequenceBifunctor
    in rightAppliedMult =~= idF Cont
rightUnitor = MkNaturalIsomorphism
    rightUnitor1
    rightUnitor2
    (\v => depLensEqToEq $ MkDepLensEq
        (\q => exEqToEq $ MkExEq Refl (\w => unitUniq _))
        (\q, w => sigEqToEq' $ MkSigEq' Refl (unitUniq w.π2))
    )
    (\_ => Refl)
public export
SequenceMonoidal : Monoidal Cont
SequenceMonoidal = MkMonoidal
    SequenceBifunctor
    I
    alpha
    leftUnitor
    rightUnitor
