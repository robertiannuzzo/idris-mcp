module Data.Container.Morphism.Closed.Tensor

import Data.Container.Morphism.Closed
import Data.Container.Tensor.Definition
public export
swap : (x ⊗ y) =&> (y ⊗ x)
swap = !! \x => swap x ## swap

public export
parallel : a =&> b -> a' =&> b' -> a ⊗ a' =&> b ⊗ b'
