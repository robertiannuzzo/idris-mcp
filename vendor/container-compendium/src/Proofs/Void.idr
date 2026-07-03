module Proofs.Void

import Proofs.Extensionality

||| All contradictions are the same
||| (something something terminal object)
export 0
allVoid : (f : Void -> a) -> (g : Void -> a)  -> f = g
allVoid f g = funExt (\case _ impossible)

||| All uninhabited functions are the same
export 0
allUninhabited : Uninhabited x => (f, g : x -> a) -> f = g
allUninhabited f g = funExt (\y => absurd y)
