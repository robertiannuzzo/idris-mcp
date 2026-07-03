module Data.Category.Bifunctor

import public Data.Category.Functor
import public Data.Category.Product
import public Data.Category.ProductCat
import public Data.Category.Notation

import Proofs

import Syntax.PreorderReasoning

%hide Prelude.(&&)
%hide Prelude.Ops.infixl.(*>)
%hide Prelude.bimap
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)

%unbound_implicits off
parameters
  {0 o1, o2, o3 : Type} (c1 : Category o1) (c2 : Category o2) (c3 : Category o3)
  public export
  Bifunctor : Type
  Bifunctor = (c1 × c2) ->> c3
  public export 0
  (-+>) : o1 -> o1 -> Type
  (-+>) = (~:>) c1
  public export 0
  (-|>) : o2 -> o2 -> Type
  (-|>) = (~:>) c2
  public export 0
  (-/>) : o3 -> o3 -> Type
  (-/>) = (~:>) c3
  private infixr 0 -+>
  private infixr 0 -|>
  private infixr 0 -/>

  parameters {a, a' : o1} {b, b' : o2}
             (f : a -+> a') (g : b -|> b')
    public export
    bimap : (bi : Bifunctor) =>
            bi.mapObj (a && b) -/> bi.mapObj (a' && b')
    bimap = bi.mapHom (a && b) (a' && b') (f && g)

  export
  bimapIdFuse :
      {a, a' : o1} -> {b, b' : o2} ->
      (f : a -+> a') -> (g : b -|> b') ->
      (bi : Bifunctor) ->
        let ab, a'b, ab', a'b' : o3
            ab = bi.mapObj (a && b)
            ab' = bi.mapObj (a && b')
            a'b = bi.mapObj (a' && b)
            a'b' = bi.mapObj (a' && b')
            m1 : ab -/> a'b
            m1 = bimap f (c2.id b)
            m2 : a'b -/> a'b'
            m2 = bimap (c1.id a') g
            end : ab -/> a'b'
            end = bimap f g
         in (m1 |> m2) {a = ab, b = a'b, c = a'b'}
         === end
  bimapIdFuse f g (MkFunctor mapObj mapHom presId presComp)
    = Calc $
      |~ (mapHom (a && b) (a' && b) (f && c2 .id b) |> mapHom (a' && b) (a' && b') (c1 .id a' && g))
      ~~ (mapHom (a && b) (a' && b') (f |> c1.id a' && c2.id b |> g))
          ..<(presComp {})
      ~~ (mapHom (a && b) (a' && b') (f && c2.id b |> g))
          ...(cong (\fid => mapHom (a && b) (a' && b') (fid && c2.id b |> g))
                   (c1.idRight {}))
      ~~ (mapHom (a && b) (a' && b') (f && g))
          ...(cong (mapHom (a && b) (a' && b') . (f &&)) (c2.idLeft {}))

  export 0
  bimapIdSwap :
      {a, a' : o1} -> {b, b' : o2} ->
      (f : a -+> a') -> (g : b -|> b') ->
      (bi : Bifunctor) ->
        let ab, a'b, ab', a'b' : o3
            ab = bi.mapObj (a && b)
            ab' = bi.mapObj (a && b')
            a'b = bi.mapObj (a' && b)
            a'b' = bi.mapObj (a' && b')
            m1 : ab -/> a'b
            m1 = bimap f (c2.id b)
            m2 : a'b -/> a'b'
            m2 = bimap (c1.id a') g
            n1 : ab -/> ab'
            n1 = bimap (c1.id a) g
            n2 : ab' -/> a'b'
            n2 = bimap f (c2.id b')
         in (m1 |> m2) {a = ab, b = a'b, c = a'b'}
         === (n1 |> n2) {a = ab, b = ab', c = a'b'}
  bimapIdSwap f g bi
    = Calc $
      |~ (bi.mapHom (a && b) (a' && b) (f && c2 .id b) |> bi.mapHom (a' && b) (a' && b') (c1 .id a' && g))
      ~~ (bi.mapHom (a && b) (a' && b') (f && g))
          ...(bimapIdFuse f g bi)
      ~~ (bi.mapHom (a && b) (a' && b') (c1.id a |> f && g))
          ..<(cong (\idf => bi.mapHom (a && b) (a' && b') (idf && g))
                   (c1.idLeft {}))
      ~~ (bi.mapHom (a && b) (a' && b') (c1.id a |> f && g |> c2.id b'))
          ..<(cong (bi.mapHom (a && b) (a' && b') . (c1.id a |> f &&))
                   (c2.idRight {}))
      ~~ (bi.mapHom (a && b ) (a && b')  (c1.id a && g) |>
          bi.mapHom (a && b') (a' && b') (f && c2.id b'))  ...(presComp {})


%unbound_implicits on
public export
assocR : (a × (b × c)) ->> ((a × b) × c)
assocR = MkFunctor
  Product.assocR
  (\k, l => Product.assocR)
  (\v => Refl)
  (\_, _, _, f, g => Refl)

public export
assocL : ((a × b) × c) ->> (a × (b × c))
assocL = MkFunctor
  Product.assocL
  (\k, l => Product.assocL)
  (\v => Refl)
  (\_, _, _, f, g => Refl)

public export
swap : {a : _} -> (a × b) ->> (b × a)
swap = MkFunctor
  Product.swap
  (\x, y => Product.swap)
  (\v => Refl)
  (\_, _, _, f, g => Refl)
public export
applyBifunctor : {0 o1, o2, o3 : Type} ->
                 {a : Category o1} ->
                 {0 b : Category o2} ->
                 {0 c : Category o3} ->
    o1 -> Bifunctor a b c -> b ->> c
applyBifunctor x mult = MkFunctor
  (curry mult.mapObj x)
  (\k, l, m => mult.mapHom (x && k) (x && l) (a.id x && m))
  (\v => mult.presId (x && v) )
  (\ax, bx, cx, f, g =>
      cong (mult .mapHom (x && ?) (x && ?)) (
      cong (&& (|:>) b f g) (sym (a.idLeft _ _ (a.id x)))) `trans`
      mult.presComp (x && ax) (x && bx) (x && cx) (a.id x && f) (a.id x && g))

public export
applyBifunctor' : {0 a : Category o} -> {b : Category o} -> o -> Bifunctor a b c -> a ->> c
applyBifunctor' x mult = MkFunctor
  (\y => mult.mapObj (y && x))
  (\k, l, m => mult.mapHom (k && x) (l && x) (m && b.id x))
  (\v => mult.presId (v && x))
  (\ax, bx, cx, f, g =>
      (cong (mult .mapHom (? && x) (? && x))
      $ cong ((|:>) a f g &&)
      $ sym $ b.idRight _ _ $ b.id x) `trans`
      mult.presComp (ax && x) (bx && x) (cx && x) (f && b.id x) (g && b.id x))
%unhide Prelude.bimap
public export
pair : a ->> b -> c ->> d -> (a × c) ->> (b × d)
pair f1 f2 =
  MkFunctor
  (bimap f1.mapObj f2.mapObj)
  (\x, y, z => f1.mapHom x.π1 y.π1 z.π1 && f2.mapHom x.π2 y.π2 z.π2 )
  (\x => cong2 (&&) (f1.presId x.π1) (f2.presId x.π2))
  (\ax, bx, cx, f, g => cong2 (&&) (f1.presComp _ _ _ f.π1 g.π1) (f2.presComp _ _ _ f.π2 g.π2))

public export
unitL : c ->> (OneCat × c)
unitL = MkFunctor (() &&) (\_, _ => (() &&)) (\v => Refl) (\a, b, c, f, g => Refl)

public export
unitR : c ->> (c × OneCat)
unitR = MkFunctor (&& ()) (\_, _ => (&& ())) (\v => Refl) (\a, b, c, f, g => Refl)

parameters
    {0 o1, o2, o3 : Type}
    {a : Category o1}
    {b : Category o2}
    {0 c : Category o3}

  public export
  applyFL : OneCat ->> a -> Bifunctor a b c -> b ->> c
  applyFL f mult = unitL ⨾⨾ pair f (idF b) ⨾⨾ mult

  public export
  applyFR : OneCat ->> b -> Bifunctor a b c -> a ->> c
  applyFR f mult = unitR ⨾⨾ pair (idF a) f ⨾⨾ mult

  -- given a bifunctor (a × b → x) and a unit category given by a single object ∈ a,
  -- and identities on that object, return the functor (b → c)
  public export
  applyL : o1 -> Bifunctor a b c -> b ->> c
  applyL x = applyFL (Const x a)

  public export
  applyR : o2 -> Bifunctor a b c -> a ->> c
  applyR x = applyFR (Const x b)
public export
ProductFunctor : {c : Category o} -> HasProduct c -> Bifunctor c c c
ProductFunctor (MkProd pair pi1 pi2 prod prodLeft prodRight uniq) = MkFunctor
  (uncurry pair)
  (\_, _, (m1 && m2) => prod ((|:>) c pi1 m1)
                             ((|:>) c pi2 m2))
-- proofs in appendix
  (\(v1 && v2) => uniq ? ? ? (c.idLeft _ _ pi1 `trans` sym (c.idRight _ _ pi1))
                       (c.idLeft _ _ _ `trans` sym (c.idRight _ _ _)))
  (\_, _, _, (f1 && f2), (g1 && g2) => uniq ? ? ?
             -- we start with
             -- ((prod (π1 ; f1) (π2 ; f2)) ; (prod (π1 ; g1) (π2 ; g2))) ; π1
     (Calc $ |~ ((prod (pi1 |> f1) (pi2 |> f2)) |> (prod (pi1 |> g1) (pi2 |> g2))) |> pi1
             -- we re-associate this expression to put the final π1 next to a `prod`
             -- prod (π1 ; f1) (π2 ; f2) ; (prod (π1 ; g1) (π2 ; g2) ; π1)
             ~~ (prod (pi1 |> f1) (pi2 |> f2)) |> ((prod (pi1 |> g1) (pi2 |> g2)) |> pi1)
                ... (sym (compAssoc c _ _ _ _ _ _ _))
             -- then we use the product axiom on the second part to get
             -- prod (π1 ; f1) (π2 ; f2) ; (π1 ; g1)
             ~~ ((prod (pi1 |> f1) (pi2 |> f2)) |> (pi1 |> g1))
                ... (cong ((prod (pi1 |> f1) (pi2 |> f2)) |>) (prodLeft _ _))
             -- then we re-associate again
             -- (prod (π1 ; f1) (π2 ; f2) ; π1) ; g1
             ~~ (((prod (pi1 |> f1) (pi2 |> f2)) |> pi1) |> g1)
                ... (compAssoc c _ _ _ _ _ _ _)
             -- Then we use our product axiom on the left part to get
             -- (π1 ; f1) ; g1
             ~~ ((pi1 |> f1) |> g1)
                ... (cong (|> g1) (prodLeft _ _))
             -- finally we reassociate to obtain
             -- π1 ; (f1 ; g1)
             ~~ pi1 |> (f1 |> g1) ...(sym (compAssoc c _ _ _ _ _ _ _))
     )

             -- ((prod (π1 ; f1) (π2 ; f2)) ; (prod (π1 ; g1) (π2 ; g2))) ; π2
     (Calc $ |~ ((prod (pi1 |> f1) (pi2 |> f2)) |> (prod (pi1 |> g1) (pi2 |> g2))) |> pi2
             -- First we re-associate to get
             -- prod (π1 ; f1) (π2 ; f2) ; ((prod (π1 ; g1) (π2 ; g2)) ; π2)
             ~~ (prod (pi1 |> f1) (pi2 |> f2))
                |>
                ((prod (pi1 |> g1) (pi2 |> g2)) |> pi2)
                ... (sym (compAssoc c _ _ _ _ _ _ _))
             -- Then we use the fact that taking the product and projecting
             -- is the same a just using the second component
             -- prod (π1 ; f1) (π2 ; f2) ; (π2 ; g2)
             ~~ (prod (pi1 |> f1) (pi2 |> f2)
                |>
                (pi2 |> g2))
                ...(cong
                    ((prod (pi1 |> f1) (pi2 |> f2)) |>)
                    (prodRight _ _))
             -- now we re-associate again to get another `prod ; π2` pattern
             -- (prod (π1 ; f1) (π2 ; f2) ; π2) ; g2
             ~~ ((prod (pi1 |> f1) (pi2 |> f2) |> pi2) |> g2)
                ...(compAssoc c _ _ _ _ _ pi2 g2)
             -- Using the same property as before we eliminate our product
             -- (π2 ; f2) ; g2
             ~~ ((pi2 |> f2) |> g2)
                ...(cong (|> g2) (prodRight _ _))
             -- We re-associate one last time to conclude the proof
             -- π2 ; (f2 ; g2)
             ~~ pi2 |> (f2 |> g2)
                ...(sym (compAssoc c _ _ _ _ _ _ _))))
public export 0
Bendo : Category o -> Type
Bendo c = c × c ->> c
