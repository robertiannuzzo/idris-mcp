module Data.Boundary

%default total
||| Type boundaries
public export
record Boundary where
  constructor MkB
  π1 : Type
  π2 : Type
public export
cartesian : Boundary -> Boundary -> Boundary
cartesian a b = (MkB (a.π1, b.π1) (a.π2, b.π2))

public export
cocartesian : Boundary -> Boundary -> Boundary
cocartesian a b = MkB (Either a.π1 b.π1) (Either a.π2 b.π2)
public export
Dup : Type -> Boundary
Dup ty = MkB ty ty

public export
BUnit : Boundary
BUnit = MkB Unit Unit
