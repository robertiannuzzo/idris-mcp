module Data.Container.Properties

import Data.Container
import Data.Container.Extension.Properties
import Data.Container.Morphism
import Data.Container.Product
import Data.Sigma
parameters {0 a, b, c : Container}
  distribAllSeq : (a * b) ▷ c =%> (a ▷ c) * (b ▷ c)
  distribAllSeq = exProduct <!
                  (\(MkEx xx yy) => \case (+> zz) => +> zz.π1 ## zz.π2
                                          (<+ zz) => <+ zz.π1 ## zz.π2)

  distribAnySeq : (a * b) ▶ c =%> (a ▶ c) ⊗ (b ▶ c)
  distribAnySeq = exProduct <!
                  (\(MkEx xx yy), (x1 && x2) =>
                      \case (+> zz) => x2 zz
                            (<+ zz) => x1 zz)

  distribPlusAllSeq : (a + b) ▶ c =%> (a ▶ c) + (b ▶ c)
  distribPlusAllSeq = exCoprod <!
                      (\case (MkEx (+> x1) x2) => \y, z => y z
                             (MkEx (<+ x1) x2) => \y, z => y z)

  distribPlusAnySeq : (a + b) ▷ c =%> (a ▷ c) + (b ▷ c)
  distribPlusAnySeq = exCoprod <!
                      (\case (MkEx (+> x1) x2) => id
                             (MkEx (<+ x1) x2) => id)
