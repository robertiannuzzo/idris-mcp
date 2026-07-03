module Data.Category.Endofunctor.Monoidal

import Data.Category
import Data.Category.Bifunctor
import Data.Category.Endofunctor
import Data.Category.Functor.Category
import Data.Category.NaturalTransformation as NT
import Data.Category.Monoid

import Syntax.PreorderReasoning
import Pipeline.Equality
parameters {0 o : Type} {c : Category o}

  0
  cMor : o -> o -> Type
  cMor = (~:>) c

  0
  (|>>) : forall x, y, z. x `cMor` y -> y `cMor` z -> x `cMor` z
  (|>>) = (|:>) c
  private infixl 1 |>>

  0
  presIdComp : (v : Endo c * Endo c) ->
    (NT.identity {f = v.π1} -⨾- NT.identity {f = v.π2})
           === NT.identity {f = v.π1 ⨾⨾ v.π2}
  presIdComp v = ntEqToEq $ MkNTEq $ \vx =>
    let
        steps : CongPipeline ? (v.π2.mapObj (v.π1.mapObj vx) `cMor` v.π2.mapObj (v.π1.mapObj vx))
        steps = (NT.identity {f = v.π1} -⨾- NT.identity {f = v.π2}).component vx
                :: AddNest  (|>> v.π2.mapHom (v.π1.mapObj vx) (v.π1.mapObj vx) (v.π1.mapHom vx vx (c.id vx)))
                            [v.π2.mapHom (v.π1.mapObj vx) (v.π1.mapObj vx) (c.id (v.π1.mapObj vx))
                            , c.id (v.π2.mapObj (v.π1.mapObj vx))]
                   [v.π2.mapHom (v.π1.mapObj vx) (v.π1.mapObj vx) (v.π1.mapHom vx vx (c.id vx))
                   , (v.π1 ⨾⨾ v.π2).mapHom vx vx (c.id vx)
                   , (NT.identity {f = v.π1 ⨾⨾ v.π2}).component vx
                   ]
    in runProof steps
      [ Refl
      , v.π2.presId (v.π1.mapObj vx)
      , c.idLeft (v.π2.mapObj (v.π1.mapObj vx)) (v.π2.mapObj (v.π1.mapObj vx)) ((v.π1 ⨾⨾ v.π2).mapHom vx vx (c.id vx))
      , Refl
      , Refl
      ]


  0
  presCompComp : (x, y, z : Endo c * Endo c) ->
                 (f : (x.π1 =>> y.π1) * (x.π2 =>> y.π2)) -> (g : (y.π1 =>> z.π1) * (y.π2 =>> z.π2)) ->
                 (f.π1 ⨾⨾⨾ g.π1) -⨾- (f.π2 ⨾⨾⨾ g.π2) === (f.π1 -⨾- f.π2) ⨾⨾⨾ (g.π1 -⨾- g.π2)
  presCompComp x y z f g = sym $ ntEqToEq $ interchange f.π1 f.π2 g.π1 g.π2
  monMultCompose :
    Bifunctor (EndoCat c) (EndoCat c) (EndoCat c)
  monMultCompose = MkFunctor
      { mapObj = (uncurry (⨾⨾))
      , mapHom = (\m1, m2, m3 => m3.π1 -⨾- m3.π2)
      , presId = presIdComp
      , presComp = presCompComp
      }
  -- proving associativity of composition of endofunctors
  F1, F2 : (EndoCat c × (EndoCat c × EndoCat c)) ->> (EndoCat c)
  F1 = (((idF (EndoCat c)) `pair` monMultCompose) ⨾⨾ monMultCompose) {b = EndoCat c × EndoCat c}
  F2 = assocR {a = EndoCat c, b = EndoCat c, c = EndoCat c} ⨾⨾ ((monMultCompose `pair` idF (EndoCat c)) ⨾⨾ monMultCompose)

  alpha1 : F1 =>> F2
  alpha1 = MkNT
    (\(m1 && (m2 && m3)) => MkNT (\vo => c.id _)
        (\x, y, m => trans (c.idLeft {}) (sym $ c.idRight {})))
    (\(a1 && (a2 && a3)), (b1 && (b2 && b3)), (f1 && (f2 && f3)) => ntEqToEq $ MkNTEq $ \xs =>
        Calc $
          |~ (c.id ?) |>>
               (f3.component (a2 .mapObj (a1 .mapObj xs)) |>>
                 (b3.mapHom ? ?
                   (f2.component (a1 .mapObj xs) |>>
                     b2.mapHom ? ? (f1 .component xs)
                   )
                 )
               )
          ~~ (f3.component (a2.mapObj (a1.mapObj xs)) |>>
               (b3.mapHom ? ?
                 (f2.component (a1.mapObj xs) |>>
                   b2.mapHom ? ? (f1.component xs)
                 )
               )
             ) ...(c.idLeft {})
          ~~ ((f3.component (a2.mapObj (a1.mapObj xs))) |>>
               ((b3.mapHom ? ?  (f2.component (a1.mapObj xs))) |>>
                 (b3.mapHom ? ?
                   (b2.mapHom ? ? (f1.component xs))
                 )
               )
             ) ...(cong ((f3.component (a2.mapObj (a1.mapObj xs))) |>>) $
                     b3.presComp {} )
          ~~ (((f3.component (a2.mapObj (a1.mapObj xs))) |>>
                   (b3.mapHom ? ? (f2.component (a1.mapObj xs)))
              ) |>> (b3.mapHom ? ? (b2.mapHom ? ? (f1.component xs)))
             ) ...(c.compAssoc {})
          ~~ ((((f3.component (a2.mapObj (a1.mapObj xs))) |>>
                   (b3.mapHom ? ? (f2.component (a1.mapObj xs)))
               ) |>> (b3.mapHom ? ? (b2.mapHom ? ? (f1.component xs)))) |>>
               (c.id ?))
             ...(sym $ c.idRight {})
    )

  alpha2 : F2 =>> F1
  alpha2 = MkNT
    (\(m1 && (m2 && m3)) => MkNT (\vo => c.id _)
        (\x, y, m => trans (c.idLeft {}) (sym $ c.idRight {})))
    (\(a1 && (a2 && a3)), (b1 && (b2 && b3)), (f1 && (f2 && f3)) => ntEqToEq $ MkNTEq $ \xs =>
        Calc $
          |~ ( (c .id (a3 .mapObj (a2 .mapObj (a1 .mapObj xs)))) |>>
                ( ((f3 .component (a2 .mapObj (a1 .mapObj xs))) |>>
                     (b3 .mapHom ? ? (f2 .component (a1 .mapObj xs)))) |>>
                  (b3 .mapHom ? ? (b2 .mapHom ? ? (f1 .component xs)))
                )
             )
          ~~ ( ( (f3 .component (a2 .mapObj (a1 .mapObj xs))) |>>
                 (b3 .mapHom ? ? (f2 .component (a1 .mapObj xs)))
               ) |>>
               (b3.mapHom ? ? (b2.mapHom (a1.mapObj xs) (b1.mapObj xs) (f1.component xs)))
             ) ...(c.idLeft {})
          ~~ ( (f3 .component (a2 .mapObj (a1 .mapObj xs))) |>>
               ( (b3 .mapHom ? ? (f2 .component (a1 .mapObj xs))) |>>
                 (b3.mapHom ? ? (b2.mapHom (a1.mapObj xs) (b1.mapObj xs) (f1.component xs)))
               )
             ) ...(sym $ c.compAssoc {})
          ~~ ( (f3 .component (a2 .mapObj (a1 .mapObj xs))) |>>
               (b3.mapHom (a2 .mapObj (a1 .mapObj xs)) (b2 .mapObj (b1 .mapObj xs))
                 ( (f2 .component (a1 .mapObj xs)) |>>
                     (b2 .mapHom (a1 .mapObj xs) (b1 .mapObj xs) (f1 .component xs))
                 )
               )
             )
            ...(sym $ cong ((f3 .component (a2 .mapObj (a1 .mapObj xs))) |>>) $
                 b3.presComp {}
               )
          ~~ (((f3 .component (a2 .mapObj (a1 .mapObj xs))) |>>
                 (b3.mapHom (a2 .mapObj (a1 .mapObj xs)) (b2 .mapObj (b1 .mapObj xs))
                   ( (f2 .component (a1 .mapObj xs)) |>>
                     (b2 .mapHom (a1 .mapObj xs) (b1 .mapObj xs) (f1 .component xs))
                   )
                 )
               ) |>>
                 (c .id (b3 .mapObj (b2 .mapObj (b1 .mapObj xs))))
             )
           ...(sym $ c.idRight {})
    )

  alpha : F1 =~= F2
  alpha = MkNaturalIsomorphism
      alpha1
      alpha2
      (\(m1 && (m2 && m3)) => ntEqToEq $ MkNTEq (\vx =>
          Calc $
            |~ (c.id (m3.mapObj (m2.mapObj (m1.mapObj vx)))) |>> (c .id (m3 .mapObj (m2 .mapObj (m1 .mapObj vx))))
            ~~ (c .id (m3.mapObj $ m2.mapObj $ m1.mapObj vx))
              ...(c.idRight {})
            ~~ m3.mapHom ? ? (c .id (m2.mapObj $ m1.mapObj vx))
              ...(sym $ m3.presId {})
            ~~ m3.mapHom ? ? (m2 .mapHom ? ? ((c.id (m1.mapObj vx))))
              ...(sym $ cong (m3.mapHom ? ?) (m2.presId {}))
            ~~ m3.mapHom ? ? (m2 .mapHom ? ? (m1 .mapHom vx vx (c .id vx)))
              ...(sym $ cong (m3.mapHom ? ? . m2.mapHom ? ?) (m1.presId {}))
          )
      )
      (\(m1 && (m2 && m3)) => ntEqToEq $ MkNTEq $ \vx =>
          Calc $
            |~ (c .id (m3 .mapObj (m2 .mapObj (m1 .mapObj vx)))) |>> (c .id (m3 .mapObj (m2 .mapObj (m1 .mapObj vx))))
            ~~ (c .id $ m3.mapObj $ m2.mapObj $ m1.mapObj vx)
               ...(c.idRight {})
            ~~ m3.mapHom ? ? (c.id $ m2.mapObj $ m1.mapObj vx)
               ...(sym $ m3.presId {})
            ~~ m3.mapHom ? ? (m2.mapHom ? ? (c.id $ m1.mapObj vx))
               ...(sym $ cong (m3.mapHom ? ?) $ m2.presId {})
            ~~ m3.mapHom ? ? (m2.mapHom ? ? (m1.mapHom vx vx (c.id vx)))
               ...(sym $ cong (m3.mapHom ? ? . m2.mapHom ? ?) $ m1.presId {})
      )

  -- left unitors
  leftUnitor1 :
      let 0 leftAppliedMult : EndoCat c ->> EndoCat c
          leftAppliedMult = applyL {a = EndoCat c, b = EndoCat c, c = EndoCat c} (idF c) monMultCompose
      in leftAppliedMult =>> idF (EndoCat c)
  leftUnitor1 = MkNT
    (\vx => MkNT
      (\_ => c.id _)
      (\x, y, m => c.idswap (vx.mapObj x) (vx.mapObj y) (vx.mapHom x y m)
      )
    )
    (\x, y, m => ntEqToEq $ MkNTEq $ \v => Calc $
        |~ ((c.id (x .mapObj v)) |>> (m .component v))
        ~~ ((m.component v) |>> c.id (y.mapObj v))
        ...(c.idswap {})
        ~~ ((m.component v) |>> (y .mapHom v v (c .id v)))
        ...(sym $ cong (m.component v |>>) (y.presId {}))
        ~~ (((m.component v) |>> (y .mapHom v v (c .id v))) |>> (c .id (y .mapObj v)))
        ...(sym $ c.idRight {})
    )



  leftUnitor2 :
      let 0 leftAppliedMult : EndoCat c ->> EndoCat c
          leftAppliedMult = applyL {a = EndoCat c, b = EndoCat c, c = EndoCat c} (idF c) monMultCompose
      in idF (EndoCat c) =>> leftAppliedMult
  leftUnitor2 = MkNT
    (\vx => MkNT
         (\v => c.id (vx.mapObj v))
         (\x, y, m => c.idswap (vx.mapObj x) (vx.mapObj y) (vx.mapHom x y m))
    )
    (\x, y, m => ntEqToEq $ MkNTEq $ \vy => Calc $
        |~ ((c.id (x.mapObj vy)) |>> (m.component vy |>> (y.mapHom vy vy (c .id vy))))
        ~~ (m.component vy |>> y.mapHom vy vy (c .id vy))
        ...(c.idLeft {})
        ~~ ((m .component vy) |>> (c .id (y .mapObj vy)))
        ...(cong ((m.component vy) |>>) (y.presId {}))
    )

  leftUnitor :
      let 0 leftAppliedMult : EndoCat c ->> EndoCat c
          leftAppliedMult = applyL {a = EndoCat c, b = EndoCat c, c = EndoCat c} (idF c) monMultCompose
      in leftAppliedMult =~= idF (EndoCat c)
  leftUnitor = MkNaturalIsomorphism
      leftUnitor1
      leftUnitor2
      (\vx => ntEqToEq $ MkNTEq $ \v =>
          (c.idLeft {})
          `trans`
          (sym $ vx.presId {})
      )
      (\vx => ntEqToEq $ MkNTEq $ \v =>
          (c.idLeft {})
          `trans`
          (sym $ vx.presId {})
      )

  -- Right unitors
  rightUnitor1 :
      let 0 rightAppliedMult : EndoCat c ->> EndoCat c
          rightAppliedMult = applyR {a = EndoCat c, b = EndoCat c, c = EndoCat c} (idF c) monMultCompose
      in rightAppliedMult =>> idF (EndoCat c)
  rightUnitor1 = MkNT
      (\vx => MkNT
          (\v => c.id (vx.mapObj v))
          (\x, y, m => c.idswap {}
          )
      )
      (\x, y, m => ntEqToEq $ MkNTEq $ \vy => sym $ c.idRight {}
      )

  rightUnitor2 :
      let 0 rightAppliedMult : EndoCat c ->> EndoCat c
          rightAppliedMult = applyR {a = EndoCat c, b = EndoCat c, c = EndoCat c} (idF c) monMultCompose
      in idF (EndoCat c) =>> rightAppliedMult
  rightUnitor2 = MkNT
      (\vx => MkNT
          (\v => c.id (vx.mapObj v))
          (\x, y, m => c.idswap {})
      )
      (\x, y, m => ntEqToEq $ MkNTEq $ \vy =>
          (c.idLeft {})
          `trans`
          (c.idswap {})
      )

  rightUnitor :
      let 0 rightAppliedMult : EndoCat c ->> EndoCat c
          rightAppliedMult = applyR {a = EndoCat c, b = EndoCat c, c = EndoCat c} (idF c) monMultCompose
      in rightAppliedMult =~= idF (EndoCat c)
  rightUnitor = MkNaturalIsomorphism
    rightUnitor1
    rightUnitor2
    (\vx => ntEqToEq $ MkNTEq $ \vy =>
        (c.idLeft {})
        `trans`
        (sym $ vx.presId {})
    )
    (\vx => ntEqToEq $ MkNTEq $ \vy =>
        (c.idLeft {})
        `trans`
        (sym $ vx.presId {})
    )
  EndoMonoidal : Monoidal (FunctorCat c c)
  EndoMonoidal = MkMonoidal
    { mult = monMultCompose
    , i = idF c
    , alpha = alpha
    , leftUnitor = leftUnitor
    , rightUnitor = rightUnitor
    }
