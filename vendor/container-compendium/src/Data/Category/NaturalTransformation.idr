module Data.Category.NaturalTransformation

import public Data.Category.Functor
import public Data.Category.Iso
import public Data.Category.Notation
import public Data.Category.Proofs
import Data.Category.Bifunctor

import Data.Iso.Category

import Control.Category as Cat

import Syntax.PreorderReasoning
import Control.Relation
import Control.Order

import Proofs.Congruence
import Proofs.DSL
import Proofs.Extensionality
import Proofs.UIP

%hide Prelude.Functor
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)

%hide Pipeline.Equality.infixr.(>|)
private infixr 7 >|

%unbound_implicits off
public export
record (=>>) {0 cObj, dObj : Type} {0 c : Category cObj} {0 d : Category dObj}
             (f, g : c ->> d) where
  constructor MkNT
  component : (v : cObj) -> f.mapObj v ~> g.mapObj v
  0 commutes : (0 x, y : cObj) -> (m : x ~> y) ->
      let -- We build each side of the naturality square
          0 top : f.mapObj x ~> g.mapObj x
          top = component x

          0 bot : f.mapObj y ~> g.mapObj y
          bot = component y

          0 left : f.mapObj x ~> f.mapObj y
          left = f.mapHom _ _ m

          0 right : g.mapObj x ~> g.mapObj y
          right = g.mapHom _ _ m

          -- And the compose them.
          0 comp1 : f.mapObj x ~> g.mapObj y
          comp1 = top |> right

          0 comp2 : f.mapObj x ~> g.mapObj y
          comp2 = left |> bot
      in comp1 === comp2
public export
identity : {0 o1, o2 : Type} -> {c : Category o1} -> {0 d : Category o2} ->
           {f : c ->> d} -> f =>> f
identity = MkNT
  (\x => f.mapHom x x (c.id x))
  (\x, y, m => let
      0 steps : CongPipeline ? (f.mapObj x ~> f.mapObj y)
      steps = (fmap (c.id x)  |> fmap m)
              :: AddNest (f.mapHom x y)
                [ (c.id x |> m)
                , m
                , (m |> c.id y)]
                [ fmap m |> fmap (c .id y) ]
      in runProof steps
          [ sym (presComp f x x y (c.id x) m),
          c.idLeft _ _ m,
          sym (c.idRight _ _ m),
          presComp f x y y m (c.id y)]
  )
public export
record NTEq
  {0 o1, o2 : Type}
  {0 c : Category o1} {0 d : Category o2}
  {f, g : c ->> d} (n1, n2 : f =>> g) where
  constructor MkNTEq
  0 sameComponent : (v : o1) -> n1.component v === n2.component v
public export
0 ntEqToEq :
  {0 o1, o2 : Type} ->
  {c : Category o1} -> {d : Category o2} ->
  {f, g : c ->> d} -> {n1, n2 : f =>> g} ->
  NTEq n1 n2 -> n1 === n2
ntEqToEq (MkNTEq sameComponent) {n1 = MkNT n1 p1} {n2 = MkNT n2 p2} =
  cong2Dep0
    {t3 = f =>> g}
    MkNT
    (funExtDep $ sameComponent)
    (funExtDep0 $ \x => funExtDep0 $ \y => funExtDep $ \z => UIP _ _)
public export
(⨾⨾⨾) :
  {0 cObj, dObj : Type} ->
  {0 c : Category cObj} -> {d : Category dObj} ->
  {f, g, h : c ->> d} ->
  f =>> g -> g =>> h -> f =>> h
(⨾⨾⨾) nat1 nat2 =
  let
    newComponent : (v : cObj) -> f.mapObj v ~> h.mapObj v
    newComponent x = nat1.component x |> nat2.component x

    0 compProof : (0 x, y : cObj) -> (m : x ~> y) ->
      let 0 n1, n2 : f.mapObj x ~> h.mapObj y
          n1 = f.mapHom x y m |> (nat1.component y |> nat2.component y)
          n2 = (nat1.component x |> nat2.component x) |> h.mapHom x y m
      in n2 === n1
    compProof x y m =
      sym (d.compAssoc {}) `trans`
      glueSquares (nat1.commutes x y m) (nat2.commutes x y m)
  in MkNT newComponent compProof
public export
-- Operator for horizontal composition
(-⨾-) : {0 o1, o2, o3 : Type} ->
        {0 a : Category o1} -> {0 b : Category o2} -> {c : Category o3} ->
        {l, k : a ->> b} ->
        {g, h : b ->> c} ->
        k =>> l ->
        g =>> h ->
        k ⨾⨾ g =>> l ⨾⨾ h
(-⨾-) nt1 nt2  =
  MkNT (\v => nt2.component (k.mapObj v) |> h.mapHom (k.mapObj v) (l.mapObj v) (nt1.component v))
  -- proof in appendix
    (\x, y, m => let
        0 H : {0 a : o2} -> {0 b : o2} ->
              a ~> b -> (h.mapObj a) ~> (h.mapObj b)
        H = h.mapHom _ _
        0 L : {0 a : o1} -> {0 b : o1} ->
              a ~> b -> (l.mapObj a) ~> (l.mapObj b)
        L = l.mapHom _ _
        0 G : {0 a : o2} -> {0 b : o2} ->
              a ~> b -> (g.mapObj a) ~> (g.mapObj b)
        G = g.mapHom _ _
        0 K : {0 a : o1} -> {0 b : o1} ->
              a ~> b -> (k.mapObj a) ~> (k.mapObj b)
        K = k.mapHom _ _
        n2 : ?
        n2 = nt1.component
        n1 : ?
        n1 = nt2.component
        0 n1p : ?
        n1p = nt2.commutes
        0 n2p : ?
        n2p = nt1.commutes
      in Calc $
      |~ ((n1 (k.mapObj x) |> H (n2 x)) |> H (L m))
      ~~ (n1 (k.mapObj x) |> (H (n2 x) |> H (L m))) ..<(c.compAssoc _ _ _ _ (n1 (k.mapObj x)) (H (n2 x)) (H (L m)))
      ~~ (n1 (k.mapObj x) |> (H (n2 x |> L m)))     ..<(cong (n1 (k.mapObj x) |> ) (h.presComp _ _ _ (n2 x) (L m)))
      ~~ (G (n2 x |> L m) |> n1 (l.mapObj y))       ...(n1p (k.mapObj x) (l.mapObj y) (n2 x |> L m))
      ~~ (G (K m |> n2 y) |> n1 (l.mapObj y))       ...(cong (\xn => G xn |> n1 (l.mapObj y)) (n2p _ _ m))
      ~~ ((G (K m) |> G (n2 y)) |> n1 (l.mapObj y)) ...(cong (\x => x |> n1 (l.mapObj y)) (g.presComp _ _ _ (K m) (n2 y)))
      ~~ (G (K m) |> (G (n2 y) |> n1 (l.mapObj y))) ..<(c.compAssoc _ _ _ _ (G (K m)) (G (n2 y)) (n1 (l.mapObj y)))
      ~~ (G (K m) |> (n1 (k.mapObj y) |> H (n2 y))) ..<(cong (G (K m) |> ) (n1p _ _ (n2 y))))
%hide Cat.Category
public export
(⨾-) : {a : Category _} -> {b : Category _} -> {c : Category _} ->
       (f : a ->> b) -> {g, h : b ->> c} ->
       g =>> h -> (f ⨾⨾ g) =>> (f ⨾⨾ h)
(⨾-) f n = identity {f}  -⨾- n
public export
(-⨾) : {0 b : Category _} -> {c : Category _} -> {d : Category _} ->
       {g, h : b ->> c} ->
       g =>> h -> (f : c ->> d) -> (g ⨾⨾ f) =>> (h ⨾⨾ f)
(-⨾) n f = n -⨾- identity {f}
public export
interchange :
   {c, d, e : Category _} ->
   {f1, g1, h1 : c ->> d} ->
   {f2, g2, h2 : d ->> e} ->
   (m1 : f1 =>> g1) ->
   (m2 : f2 =>> g2) ->
   (n1 : g1 =>> h1) ->
   (n2 : g2 =>> h2) ->
   NTEq ((m1 -⨾- m2) ⨾⨾⨾ (n1 -⨾- n2)) ((m1 ⨾⨾⨾ n1) -⨾- (m2 ⨾⨾⨾ n2))
-- Proof in appendix
interchange m1 m2 n1 n2 = MkNTEq $ \z =>
    let m1c : (x : _) -> f1.mapObj x ~> g1.mapObj x
        m1c = m1.component
        m2c : (x : _) -> f2.mapObj x ~> g2.mapObj x
        m2c = m2.component
        n1c : (x : _) -> g1.mapObj x ~> h1.mapObj x
        n1c = n1.component
        n2c : (x : _) -> g2.mapObj x ~> h2.mapObj x
        n2c = n2.component
        steps : CongPipeline ? ((f1 ⨾⨾ f2).mapObj z ~> (h1 ⨾⨾ h2).mapObj z)
        steps =
                ((m1 -⨾- m2) ⨾⨾⨾ (n1 -⨾- n2)).component z
             :: ((m1 -⨾- m2).component z |> (n1 -⨾- n2).component z)
             :: ((m2c (f1.mapObj z) |> fmap (m1c z)) |> (n1 -⨾- n2).component z)
             :: ((m2c (f1.mapObj z) |> fmap (m1c z)) |> (n2c (g1.mapObj z) |> h2.mapHom _ _ (n1c z)))
             :: Cong (|> h2.mapHom _ _ (n1c z))
                     ( (((m2c (f1.mapObj z) |> g2.mapHom _ _ (m1c z)) |> n2c (g1.mapObj z)))
                     :: Cong (m2c (f1.mapObj z) |>)
                             [ (g2.mapHom _ _ (m1c z) |> n2c (g1.mapObj z))
                             , (n2c (f1.mapObj z) |> h2.mapHom _ _ (m1c z))]
                     >| [((m2c (f1.mapObj z) |> n2c (f1.mapObj z)) |> h2.mapHom _ _ (m1c z))]
                     )
             >| Cong ((m2c (f1.mapObj z) |> n2c (f1.mapObj z)) |>)
                    [ (h2.mapHom _ _ (m1c z) |> h2.mapHom _ _ (n1c z))
                    , ((h2.mapHom _ _ (m1c z |> n1c z)))]
             >| [((m1 ⨾⨾⨾ n1) -⨾- (m2 ⨾⨾⨾ n2)).component z]
  in runProof steps
  [Refl , Refl , Refl
  , e.compAssoc {}
  , sym (e.compAssoc {})
  , sym (n2.commutes {})
  , e.compAssoc {}
  , sym (e.compAssoc {})
  , sym (h2.presComp {})
  , Refl]
public export
record (=~=)
  {0 o1, o2 : Type}
  {0 c : Category o1} {0 d : Category o2}
  (0 f, g : c ->> d) where
  constructor MkNaturalIsomorphism
  nat : f =>> g
  tan : g =>> f
  0 η_φ : (v : o1) ->
    (nat.component v |> tan.component v) {a = (f.mapObj v), b = (g.mapObj v), c = (f.mapObj v)}
       === d.id (f.mapObj v)
  0 φ_η : (v : o1) ->
    (tan.component v |> nat.component v) {a = (g.mapObj v), b = (f.mapObj v), c = (g.mapObj v)}
       === d.id (g.mapObj v)
public export
symNT :
  {0 o1, o2 : Type} -> {0 c : Category o1} -> {0 d : Category o2} ->
  {0 f, g : c ->> d} -> f =~= g -> g =~= f
symNT nt = MkNaturalIsomorphism nt.tan nt.nat nt.φ_η nt.η_φ
public export
transNT :
  {0 o1, o2 : Type} ->
  {0 c : Category o1} -> {d : Category o2} ->
  {f, g, h : c ->> d} ->
  f =~= g -> g =~= h -> f =~= h
transNT nt mt = MkNaturalIsomorphism
  (nt.nat ⨾⨾⨾ mt.nat)
  (mt.tan ⨾⨾⨾ nt.tan)
  -- Proofs in appendix
  (\x => let
    ntc : f.mapObj x ~> g.mapObj x
    ntc = nt.nat.component x
    ntc' : g.mapObj x ~> f.mapObj x
    ntc' = nt.tan.component x
    mtc : g.mapObj x ~> h.mapObj x
    mtc = mt.nat.component x
    mtc' : h.mapObj x ~> g.mapObj x
    mtc'= mt.tan.component x

    0 steps : CongPipeline ? (f.mapObj x ~> f.mapObj x)
    steps =
         -- first we associate to the right
         ((ntc |> mtc) |> (mtc' |> ntc'))
         -- then we're congruent over (ntc|>)
         :: Cong (ntc |>)
                  --then we associate to the left
                 ((mtc |> (mtc' |> ntc'))
                 -- now we're congruent over (|> ntc')
                 :: Cong (|> ntc')
                      -- we apply the rule we have
                      [ mtc |> mtc'
                      , d.id (g.mapObj x)]
                 -- then remove the extra identity on the left
                 >| [ntc']
                 )
        -- finally we apply the other rule
         >| [ntc |> ntc'
            , d.id (f .mapObj x)
            ]
    in runProof steps
        [ sym (d.compAssoc {})
        , d.compAssoc {}
        , mt.η_φ  x
        , d.idLeft {}
        , Refl
        , nt.η_φ x
        ]
  )
  (\x => let
    ntc : f.mapObj x ~> g.mapObj x
    ntc = nt.nat.component x
    ntc' : g.mapObj x ~> f.mapObj x
    ntc' = nt.tan.component x
    mtc : g.mapObj x ~> h.mapObj x
    mtc = mt.nat.component x
    mtc' : h.mapObj x ~> g.mapObj x
    mtc'= mt.tan.component x

    0 steps : CongPipeline ? (h.mapObj x ~> h.mapObj x)
    steps =
      ( ((mtc' |> ntc') |> (ntc |> mtc))
      :: Cong (mtc' |>)
             ( (ntc' |> (ntc |> mtc))
             :: Cong (|> mtc)
                 [ (ntc' |> ntc)
                 , (d.id (g.mapObj x))
                 ]
             >| [mtc]
             )
      >| [d.id (h.mapObj x)])
    in runProof steps
        [ sym (d.compAssoc {})
        , d.compAssoc {}
        , nt.φ_η x
        , d.idLeft {}
        , mt.φ_η x
        ]
  )
%unbound_implicits on
public export
{a : _} -> Reflexive (a ->> b) (=>>) where
  reflexive = identity

public export
{b : _} -> Transitive (a ->> b) (=>>) where
  transitive f g = f ⨾⨾⨾ g

export
{a, b : _} -> Preorder (a ->> b) (=>>) where
