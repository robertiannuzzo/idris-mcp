module Proofs.Unit

import Proofs.Extensionality

public export
unitUniq : (x : Unit) -> MkUnit === x
unitUniq () = Refl

public export
unitApp : (f : Unit -> a) -> (x : Unit) -> f x === f ()
unitApp f () = Refl

public export 0
unitApp' : {0 a : Type} -> {0 f : Unit -> a} -> (\x : Unit => f x) === (\_ : Unit=> f ())
unitApp' = funExt $ \() => Refl

