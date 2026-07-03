module Data.Category.Functor.Exponential

import Data.Category.Bifunctor
import Data.Category.Functor.Category
import Data.Category.Product
import Data.Category.NaturalTransformation

import Syntax.PreorderReasoning
curryFunctor : {0 o : Type} -> {c : Category o} ->
               a ->> (FunctorCat b c) -> (a × b) ->> c
curryFunctor (MkFunctor mo mm pid pcomp) =
  let (|>>) : {x, y, z : o} -> x ~> y -> y ~> z -> x ~> z
      (|>>) = (|:>) c
      private infixr 2 |>>
  in MkFunctor
    (\(x && y) => (mo x).mapObj y)
    (\(x && x'), (y && y'), (m && m') =>
        (mo x).mapHom x' y' m' |>> (mm x y m).component y')
    (\(x && y) => let
        ff = (mo x).presId y
        fg = (mo x).presComp y y y
        0 nt = (mm x x (a.id x)).commutes y y (b.id y)
        cc : {v1, v2, v3 : o} -> v1 ~> v2 -> v2 ~> v3 -> v1 ~> v3
        cc = (|:>) c
        in Calc $
        |~ (((mo x).mapHom y y (b.id y))
            |>>
            ((mm x x (a.id x)).component y)
           )
        ~~ (((mm x x (a .id x)) .component y)
             |>>
            ((mo x) .mapHom y y (b .id y))
           ) ..<(nt)
        ~~ (c.id (mapObj (mo x) y) |>> (mo x).mapHom y y (b.id y))
            ...(cong
                   (\vx => cc vx ((mo x).mapHom y y (b.id y)))
                   (let vs = (mo x).presId y
                      ; pp = pid x
                    in (cong (\vx => vx.component y) pp) `trans` vs)
               )
        ~~ (mo x).mapHom y y (b.id y) ...(c.idLeft _ _ ((mo x).mapHom y y (b.id y)))
        ~~ c.id ((mo x).mapObj y) ...(ff)
    )
    (\(x1 && x2), (y1 && y2), (z1 && z2), (m1 && m2), (n1 && n2) =>
        Calc $
        |~ (((mo x1) .mapHom x2 z2 ((|:>) b m2 n2)) |>> ((mm x1 z1 ((|:>) a m1 n1)) .component z2))
        ~~ ((((mo x1).mapHom x2 y2 m2) |>> ((mo x1).mapHom y2 z2 n2)) |>>
            (((mm x1 y1 m1).component z2) |>> ((mm y1 z1 n1).component z2)))
          ...(cong2 (|>>)
                ((mo x1).presComp _ _ _ m2 n2)
                (cong (\vx => vx.component z2) (pcomp _ _ _ m1 n1))
             )
        ~~ (((mo x1).mapHom x2 y2 m2) |>> (((mo x1).mapHom y2 z2 n2) |>>
            (((mm x1 y1 m1) .component z2) |>> ((mm y1 z1 n1).component z2))))
            ..<(c.compAssoc _ _ _ _
                   ((mo x1).mapHom x2 y2 m2)
                   ((mo x1).mapHom y2 z2 n2)
                   (((mm x1 y1 m1) .component z2) |>> ((mm y1 z1 n1) .component z2)))
        ~~ (((mo x1).mapHom x2 y2 m2) |>>
            ((((mo x1).mapHom y2 z2 n2) |>> ((mm x1 y1 m1) .component z2)) |>>
            ((mm y1 z1 n1) .component z2)))
            ...(cong (((mo x1).mapHom x2 y2 m2) |>>) (c.compAssoc {}))
        ~~ (((mo x1).mapHom x2 y2 m2) |>>
            ((((mm x1 y1 m1).component y2) |>> ((mo y1).mapHom y2 z2 n2)) |>>
            ((mm y1 z1 n1) .component z2)))
            ..<(cong
                 (\vx => ((mo x1).mapHom x2 y2 m2) |>> (vx |>> ((mm y1 z1 n1) .component z2)))
                 ((mm x1 y1 m1).commutes y2 z2 n2))
        ~~ (((mo x1).mapHom x2 y2 m2) |>> (((mm x1 y1 m1).component y2) |>>
            (((mo y1).mapHom y2 z2 n2) |>> ((mm y1 z1 n1).component z2))))
            ..<(cong ((mo x1).mapHom x2 y2 m2 |>>) (c.compAssoc {}))
        ~~ ((((mo x1).mapHom x2 y2 m2) |>> ((mm x1 y1 m1).component y2)) |>>
            (((mo y1).mapHom y2 z2 n2) |>> ((mm y1 z1 n1).component z2)))
           ...(c.compAssoc {})
    )

public export
uncurryFunctor :
    {0 o, p, q : Type} ->
    {a : Category p} -> {b : Category q} -> {c : Category o} ->
    (a × b) ->> c -> a ->> (FunctorCat b c)
    -- Proof in appendix
uncurryFunctor (MkFunctor mo mm pid pcomp) = MkFunctor
    (\vx => MkFunctor
        (\vy => mo (vx && vy))
        (\vy, vz, m =>
            mm (vx && vy) (vx && vz) (a.id vx && m))
        (\vy => Calc $
             |~ mm (vx && vy) (vx && vy) (a.id vx && b.id vy)
             ~~ c.id (mo (vx && vy))
             ...(pid (vx && vy))
        )
        (\vy, vz, vw, f, g => let
            gn = pcomp (vx && vy) (vx && vz) (vx && vw)
                   (a.id vx && f) (a.id vx && g)
            in Calc $
            |~ mm (vx && vy) (vx && vw) (a.id vx && (|:>) b f g)
            ~~ mm (vx && vy) (vx && vw)
                ((|:>) a (a.id vx) (a.id vx) && (|:>) b f g)
            ..<(cong (mm (vx && vy) (vx && vw)) $
                cong2 (&&) (a.idRight _ _ _) Refl)
            ~~ (|:>) c
                  (mm (vx && vy) (vx && vz) (a.id vx && f))
                  (mm (vx && vz) (vx && vw) (a.id vx && g))
            ...(gn)
        )
    )
    (\vx, vy, m => MkNT
        (\vz => mm (vx && vz) (vy && vz) (m && b.id vz))
        (\vz, vw, mx => let
               pq = pcomp (vx && vz) (vx && vw) (vy && vw)
                          (a.id vx && mx) (m && b.id vw)
               pp = pcomp (vx && vz) (vy && vz) (vy && vw)
                          (m && b.id vz) (a .id vy && mx)
            in Calc $
            |~ (|:>) c
               (mm (vx && vz) (vy && vz) (m && b.id vz))
               (mm (vy && vz) (vy && vw) (a .id vy && mx))

            ~~ mm (vx && vz) (vy && vw)
                  ((|:>) a m (a.id vy) && (|:>) b (b.id vz) mx)
               ..<(pp)
            ~~ mm (vx && vz) (vy && vw)
                  (m && mx)
               ...(cong (mm (vx && vz) (vy && vw)) $
                   cong2 (&&) (a.idRight _ _ m) (b.idLeft _ _ mx))
            ~~ mm (vx && vz) (vy && vw)
                  ((|:>) a (a.id vx) m && (|:>) b mx (b.id vw))
               ..<(cong (mm (vx && vz) (vy && vw)) $
                   cong2 (&&)
                       (a.idLeft _ _ m)
                       (b.idRight _ _ mx))
            ~~ (|:>) c
               (mm (vx && vz) (vx && vw) (a.id vx && mx))
               (mm (vx && vw) (vy && vw) (m && b.id vw))
               ...(pq)
        )
    )
    (\vx => ntEqToEq $ MkNTEq $ \vy => Refl)
    (\vx, vy, vz, f, g => ntEqToEq $ MkNTEq $ \vw => let
          qq = pcomp (vx && vw) (vy && vw) (vz && vw) (f && b.id vw) (g && b.id vw)
          in Calc $
          |~ (mm (vx && vw) (vz && vw) ((|:>) a f g && b.id vw))
          ~~ (mm (vx && vw) (vz && vw) ((|:>) a f g && (|:>) b (b.id vw) (b.id vw)))
          ..<(cong (mm (vx && vw) (vz && vw)) $
              cong2 (&&) Refl (b.idLeft _ _ _))
          ~~ (|:>) c
              (mm (vx && vw) (vy && vw) (f && b.id vw))
              (mm (vy && vw) (vz && vw) (g && b.id vw))
          ...(qq)
    )
