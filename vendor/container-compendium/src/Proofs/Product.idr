module Proofs.Product

import Data.Product
import Data.Iso

export
prodUniq : (x : a * b) -> x.π1 && x.π2 = x
prodUniq (p1 && p2) = Refl

public export
assocLR : (x : (a * b) * c) -> assocR (assocL x) === x
assocLR ((xa && xb) && xc) = Refl
public export
assocRL : (x : a * (b * c)) -> assocL (assocR x) === x
assocRL (xa && (xb && xc)) = Refl
public export
assocIso : (a * (b * c)) ≅ ((a * b) * c)
assocIso = MkIso assocR assocL assocLR assocRL
public export
symIso : a * b ≅ b * a
symIso = MkIso swap swap prodUniq prodUniq

public export
leftUnitIso : () * a ≅ a
leftUnitIso = MkIso
  π2
  (() &&)
  (\_ => Refl)
  (\(() && a) => Refl)

public export
rightUnitIso : a * () ≅ a
rightUnitIso = transIso symIso leftUnitIso
