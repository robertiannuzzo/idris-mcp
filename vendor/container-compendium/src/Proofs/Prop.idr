module Proofs.Prop

import Data.Ops

%hide Builtin.Equal
data Equal : forall a, b . a -> b -> Type where
     [search a b]
     Refl : {0 x : a} -> Equal x x
(===) : (x : a) -> (y : a) -> Type
(===) = Equal

(~=~) : (x : a) -> (y : b) -> Type
(~=~) = Equal
