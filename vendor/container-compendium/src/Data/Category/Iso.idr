module Data.Category.Iso

import Data.Category
import Data.Iso
public export
IsoCat : Category Type
IsoCat = NewCat
  { objects = Type
  , morphisms = (≅)
  , identity = (\x => Iso.identity _)
  , composition = transIso
  , identity_right = (\x => fromIsoEq _ _ (isoIdRight x))
  , identity_left = (\x => fromIsoEq _ _ (isoIdLeft x))
  , compose_assoc = (\x, y, z => fromIsoEq _ _ (transIsoAssoc x y z))
  }
