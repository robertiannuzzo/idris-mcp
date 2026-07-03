module Data.MaybeCoprod

import Data.Coproduct
import Data.Iso

public export
maybeToCoprod : Maybe a -> () + a
maybeToCoprod Nothing = <+ ()
maybeToCoprod (Just x) = +> x

public export
coprodToMaybe : () + a -> Maybe a
coprodToMaybe (<+ x) = Nothing
coprodToMaybe (+> x) = Just x

public export
maybeCoprodIso : {0 a : Type} -> Maybe a ≅ () + a
maybeCoprodIso = MkIso
    maybeToCoprod
    coprodToMaybe
    (\case (+> xx) => Refl
           (<+ ()) => Refl)
    (\case Nothing => Refl
           (Just x) => Refl)

