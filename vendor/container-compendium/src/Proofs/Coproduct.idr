module Proofs.Coproduct

import Data.Coproduct
import Data.Iso

public export
assocIso : Iso (a + (b + c)) ((a + b) + c)
assocIso = MkIso assocL assocR assocRLR assocLRL
