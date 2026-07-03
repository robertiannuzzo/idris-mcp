module Optics.Existential

||| existential lenses as defined in the Open games project
public export
record Lens (x, y, s, r : Type) where
  constructor MkLens
  0 z : Type
  view : x -> (z, s)
  update : (z, r) -> y

||| Composition of existential lenses
public export
compose : Lens x y s r -> Lens s r t u -> Lens x y t u
compose (MkLens t1 v1 u1) (MkLens t2 v2 u2) = MkLens
  (Pair t1 t2)
  (\x => let val = v1 x ; val2 = v2 (snd val) in ((fst val, fst val2), snd val2))
  (\x => u1 (fst (fst x), u2 (snd (fst x), snd x)))


nil : Lens (List x) (List y) (List s) (List r)
nil = MkLens Unit (const ((),[])) (const [])

partial
cons : Lens x y s r -> Lens (List x) (List y) (List s) (List r) -> Lens (List x) (List y) (List s) (List r)
cons (MkLens t1 g1 s1) (MkLens t2 g2 s2) = MkLens
  (Pair t1 t2)
  (\(x :: xs) =>
    let v1 = g1 x ; v2 = g2 xs in
        ((fst v1, fst v2), snd v1 :: snd v2))
  (\((t1, t2), x :: xs)  =>
    let v1 = s1 (t1, x) ; v2 = s2 (t2, xs) in v1 :: v2)

||| Partial function to turn a list of lenses into a lens of lists
partial
lists : List (Lens x y s r) -> Lens (List x) (List y) (List s) (List r)
lists = foldr cons nil

