module Proofs.Extensionality

export
0 funExt : {f, g : a -> b} -> ((x : a) -> f x === g x) ->  f === g
export
0 funExtDep : {a : Type} -> {b : a -> Type} -> {f, g : (x : a) -> b x} ->
              ((x : a) -> f x === g x) ->  f === g
export 0
hfunExt : {f : a -> b} -> {g : c -> b} -> (prf : a === c) -> ((x : a) -> f x === g (replace {p=Basics.id} prf x)) ->  f === replace {p = \x => x -> b} (sym prf) g
hfunExt Refl = funExt

export 0
funExtDep0 : {a : Type} -> {b : a -> Type} -> {f, g : (0 x : a) -> b x} -> ((0 x : a) -> f x = g x) ->  f = g

export
0 funExt2Dep : {a : Type} -> {b : a -> Type} -> {c : a -> Type} -> {f, g : (x : a) -> b x -> c x} -> ((x : a) -> (y : b x) -> f x y = g x y) ->  f = g


export 0
funExt2 : {f, g : a -> b -> c} -> ((x : a) -> (y : b) -> f x y = g x y) ->  f = g


export
applySame : {f, g : a -> b} -> (x : a) -> f === g -> f x === g x
applySame x Refl = Refl
