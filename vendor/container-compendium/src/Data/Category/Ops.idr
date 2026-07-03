module Data.Category.Ops

-- NOTE(idris-mcp vendoring): this file's original form declares fixity for
-- a number of Unicode operators (⨾, ∘/○, ▷, ▶, ⊗, ×, ◁, and combinations).
-- No current Idris2 (stable 0.8.0 or the pack-pinned nightly as of
-- 2026-06-22) accepts non-ASCII operator characters: `isOpChar` in
-- Core/Name.idr is a fixed ASCII whitelist. Those declarations are commented
-- out below rather than deleted, since this is a vendored copy scoped to
-- Data.Container/.Extension/.Morphism.Chart, which don't need them. See
-- idris-mcp's own project notes for the full finding.

export infixr 1 ~>   -- Morphisms
export infix 1 <!    -- Container morphism constructor
export infixl 5 |>   -- forward Composition
-- export infixl 5 ⨾    -- forward Composition
-- export infixr 5 •    -- reverse Composition
-- export infixr 7 ⨾⨾  -- Functor composition
-- export infixr 7 ⨾⨾⨾  -- natural transformation composition
export infix 3 <>
export infixr 7 ><    -- Product
-- export infixr 7 ~><~    -- Product
export infix 5 :-

export infixr 4 >>-
export infixr 4 -<<

export infix 1 =~= -- Isomorphisms

export infixr 5 ->> -- Functor
export infixr 4 =>> -- Natural Transformations

-- container things
-- export infixl 6 ○
-- export infixl 6 ▷ -- sequential composition of containers
-- export infixl 6 ▶ -- sequential composition of containers
-- export infixr 10 • -- application
-- export infixl 6 ~○~
-- export infixl 6 ~○#~
-- export infixl 7 ⊗   -- monoidal product operator
-- export infixl 7 ~⊗~ -- container tensor product bifunctor
-- export infixl 7 -⊗- -- monoidal product map on morphisms
-- export infixl 7 ~*~
-- export infixl 7 ~▶~
-- export infixl 7 ~▷~
-- export prefix 7 ▷~  -- sequence functor
-- export prefix 7 ~▷  -- sequence functor
-- export infixl 7 ~▷#~
-- export infixl 7 ~▶#~ -- forall composition bifunctor in ContCart
-- export infixl 7 ~▷#~
-- export infixl 6 ×
export typebind infixr 0 !>
-- export typebind infixr 0 ▷
-- export infixr 0 ◁
-- export infixl 9 -⨾- -- horizontal composition
-- export infixl 6 ~+~
export infixl 1 -.-
-- export infixl 1 -⨾ -- left whiskering
-- export infixl 1 ⨾- -- right whistering
-- cartesian containers
export infixr 0 =#> -- morphisms
export infixl 1 |#> -- composition

export infixr 1 =%> -- morphisms
export infixl 1 |%> -- composition

export infixr 1 =&> -- morphisms
export infixl 1 |&> -- composition

export prefix 1 !! -- closed lens constructor
