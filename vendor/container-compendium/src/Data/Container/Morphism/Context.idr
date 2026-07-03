module Data.Container.Morphism.Context

import Data.Container.Definition
import Data.Container.Morphism.Definition
public export
State : Container -> Type
State a = I =%> a
public export
(.getVal) : State a -> a.request
(.getVal) m = m.fwd ()
public export
state : a.request -> State a
state x = const x <! (const (const ()))
public export
Costate : Container -> Type
Costate a = a =%> I
public export
runCostate : Costate a -> (x : a.request) -> a.response x
runCostate m x = m.bwd x ()
public export
costate : ((x : a.request) -> a.response x) -> Costate a
costate f = const () <! (\x => const (f x))
