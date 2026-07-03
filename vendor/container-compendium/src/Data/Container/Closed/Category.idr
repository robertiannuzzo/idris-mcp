module Data.Container.Closed.Category

import Data.Container.Definition
import Data.Container.Closed
import Data.Container.Closed.Eq

import Data.Category

public export
Cont : Category Container
Cont = NewCat Container
  (=&>)
  (\x => identity x)
  (|&>)
  (\a => clsEqToEq SigEq sigEqToEq $ MkClsEq $ \y => MkSigEq Refl (IRefl Refl))
  (\a => clsEqToEq SigEq sigEqToEq $ MkClsEq $ \y => MkSigEq Refl (IRefl Refl))
  (\x, y, z => clsEqToEq SigEq sigEqToEq $ MkClsEq $ \y => MkSigEq Refl (IRefl Refl))

