module Proofs.Preorder

public export
transIdLeft : (a : x === y) -> Refl `trans` a = a
transIdLeft Refl = Refl

public export
transIdRight : (a : x === y) -> a `trans` Refl = a
transIdRight Refl = Refl

public export
congId : (a : x === y) -> Prelude.cong Prelude.id a === a
congId Refl = Refl

