module Proofs.Congruence

public export
congDep : {t : Type} -> {u : t -> Type} -> {0 a, b : t} ->
          (0 f : ((x : t) -> u x)) -> (0 _ : a === b) -> f a = f b
congDep f Refl = Refl


public export
cong2Dep :
  {0 t1 : Type} ->
  {0 t2 : t1 -> Type} ->
  (f : ((x : t1) -> t2 x -> t3)) ->
  {0 a, b : t1} -> {0 c : t2 a} -> {0 d : t2 b} ->
  (p : a === b) -> c ~=~ d -> f a c = f b d
cong2Dep f Refl Refl = Refl


public export
cong2Dep' :
  {0 t1 : Type} ->
  {0 t2 : t1 -> Type} ->
  (f : ((x : t1) -> t2 x -> t3)) ->
  {0 a, b : t1} ->
  {0 c : t2 a} ->
  {0 d : t2 b} ->
  (p : a === b) ->
  c === (rewrite p in d) ->
  f a c = f b d
cong2Dep' f Refl Refl = Refl

public export
cong2Dep0 :
  {0 t1 : Type} ->
  {0 t2 : t1 -> Type} ->
  (f : ((x : t1) -> (0 _ : t2 x) -> t3)) ->
  {0 a, b : t1} ->
  {0 c : t2 a} ->
  {0 d : t2 b} ->
  (p : a === b) ->
  c === (rewrite p in d) ->
  f a c = f b d
cong2Dep0 f Refl Refl = Refl

public export
cong2Depp :
  {0 t1 : Type} ->
  {0 t2 : t1 -> Type} ->
  {0 t3 : t1 -> Type} ->
  (f : ((x : t1) -> t2 x -> t3 x)) ->
  {0 a, b : t1} -> {0 c : t2 a} -> {0 d : t2 b} ->
  (p : a === b) ->
  (q : c === (rewrite p in d)) ->
  f a c = f b d
cong2Depp f Refl Refl = Refl

public export
cong2Deppp :
  {0 t1 : Type} ->
  {0 t2 : t1 -> Type} ->
  {0 t3 : (y : t1) -> t2 y-> Type} ->
  (f : ((x : t1) -> (y : t2 x) -> t3 x y)) ->
  {0 a, b : t1} -> {0 c : t2 a} -> {0 d : t2 b} ->
  (p : a === b) -> c === (rewrite p in d) -> f a c = f b d
cong2Deppp f Refl Refl = Refl

public export
cong3 : (0 f : (t1 -> t2 -> t3 -> u)) ->
        a = b -> c = d -> x = y -> f a c x = f b d y
cong3 f Refl Refl Refl = Refl

public export
app : {f, g : a -> b}  -> f === g -> (x : a) -> f x === g x
app Refl x = Refl

public export 0
appDep : {a : Type} -> {b : a -> Type} ->
         {f, g : (x : a) -> b x}  -> f === g -> (x : a) -> f x === g x
appDep Refl x = Refl

public export
arg : {0 a : Type} -> {0 b : a -> Type} ->
      (f : (x : a) -> b x) -> (x, y : a) -> (p : x === y) -> replace {p = b} p (f x) === (f y)
arg f x x Refl = Refl

public export
fn : {0 a : Type} -> {0 a', b' : a -> Type} ->
     (f : (x : a) -> a' x) ->
     (g : (x : a) -> b' x) ->
     (pt : a' = b') ->
     (pf : f === rewrite__impl (\x : (a -> Type) => (y : a) -> x y) pt g) ->
     (x, y : a) -> (p : x === y) -> f x ~=~ g y
fn f f Refl Refl x x Refl = Refl

fn' : {0 a : Type} -> {0 a', b' : a -> Type} ->
     (f : (x : a) -> a' x) ->
     (g : (x : a) -> b' x) ->
     (pt : a' = b') ->
     (pf : f ~=~ g) ->
     (x, y : a) -> (p : x === y) -> f x ~=~ g y
fn' f f Refl Refl x x Refl = Refl

public export
arg' : {0 a : Type} -> {0 b : a -> Type} ->
      (f : (x : a) -> b x) -> (x, y : a) -> (p : x === y) -> f x ~=~ f y
arg' f x x Refl = Refl
