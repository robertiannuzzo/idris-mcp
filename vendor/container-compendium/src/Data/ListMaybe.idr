module Data.ListMaybe

import Data.Distributive
import Data.List
import Data.Category.NaturalTransformation
import Data.Category.Monad

import Pipeline.Equality

%hide AddFunc.(::)

%unbound_implicits on

public export
maybeBind : Maybe a -> (a -> Maybe b) -> Maybe b
maybeBind (Just x) f = f x
maybeBind Nothing x = Nothing

maybeBindJoin : (x : Maybe a) -> (f : a -> Maybe b) -> maybeBind x f === joinMaybe (map f x)
maybeBindJoin Nothing f = Refl
maybeBindJoin (Just x) f = Refl

public export
distribListMaybe : List (Maybe a) -> Maybe (List a)
distribListMaybe [] = Just []
distribListMaybe (x :: xs) = maybeBind x $ \v =>  map (v ::) (distribListMaybe xs)

square : (f : (a -> b)) ->
         (x : List (Maybe a)) ->
         distribListMaybe (map (map f) x) = map (map f) (distribListMaybe x)
square f [] = Refl
square f (Nothing :: xs) = Refl
square f ((Just x) :: xs) with (square f xs)
  _ | pat = let xx = sym (maybeFunctorCompose (map f) (x ::) (distribListMaybe xs))
                yy = maybeFunctorCompose (f x ::) (map f) (distribListMaybe xs)
            in trans (cong (map (f x ::)) pat)
             $ trans yy xx

%unbound_implicits off
--                   l
--           L M M ────────── M L M
--             │                │
--  (η η x ::) │                │ M l
--             V                V
--           L M M            M M L
--             │                │
--           l │                │ M M (x ::)
--             V                V
--           M L M ─────────> M M L
--                     M l
doubleDistCommutes :  {0 a : Type} -> (x : a) -> let
  --  top-right corner
  top : List (Maybe (Maybe a)) -> Maybe (List (Maybe a))
  top = distribListMaybe
  topRight : Maybe (List (Maybe a)) -> Maybe (Maybe (List a))
  topRight = map distribListMaybe
  botRight : Maybe (Maybe (List a)) -> Maybe (Maybe (List a))
  botRight = map (map (x ::))

  -- bottom-left corner
  topLeft : List (Maybe (Maybe a)) -> List (Maybe (Maybe a))
  topLeft = (Just (Just x) ::)
  botLeft : List (Maybe (Maybe a)) -> Maybe (List (Maybe a))
  botLeft = distribListMaybe
  bottom : Maybe (List (Maybe a)) -> Maybe (Maybe (List a))
  bottom = map distribListMaybe

  in (xs : List (Maybe (Maybe a))) ->
     bottom (botLeft (topLeft xs)) === botRight (topRight (top xs))
doubleDistCommutes x [] = Refl
doubleDistCommutes x (Nothing :: xs) = Refl
doubleDistCommutes x ((Just Nothing) :: xs) with (distribListMaybe xs)
  doubleDistCommutes x ((Just Nothing) :: xs) | Nothing = Refl
  doubleDistCommutes x ((Just Nothing) :: xs) | (Just y) = Refl
doubleDistCommutes x ((Just (Just y)) :: xs) with (distribListMaybe xs)
  doubleDistCommutes x ((Just (Just y)) :: xs) | Nothing = Refl
  doubleDistCommutes x ((Just (Just y)) :: xs) | (Just z) = Refl


distribConsCommutes : {0 a : Type} ->
  (x : a) -> (xs : List (Maybe a)) ->
  distribListMaybe (Just x :: xs) === map (x ::) (distribListMaybe xs)
distribConsCommutes x [] = Refl
distribConsCommutes x (y :: xs) = Refl


0
pentagon1 : {0 a : Type} -> (x : List (Maybe (Maybe a))) ->
        joinMaybe (map distribListMaybe (distribListMaybe x)) =
          distribListMaybe (map joinMaybe x)
pentagon1 [] = Refl
pentagon1 (Nothing :: xs) = Refl
pentagon1 ((Just Nothing) :: xs) with (distribListMaybe xs)
  pentagon1 ((Just Nothing) :: xs) | Nothing = Refl
  pentagon1 ((Just Nothing) :: xs) | (Just x) = Refl
pentagon1 ((Just (Just x)) :: xs) = let
    steps : CongPipeline ? (List (Maybe (Maybe a)) -> Maybe (List a))
    steps =
         Cong (joinMaybe .) (Cong (. distribListMaybe)
                                  [ map distribListMaybe . map {f = Maybe} (Just x ::)
                                  , map (distribListMaybe . (Just x ::))
                                  , map ((map (x ::)) . distribListMaybe)
                                  , map (map (x ::)) . map distribListMaybe ]
                            >| [map distribListMaybe . distribListMaybe . (Just (Just x) ::) ])
      >| Cong (. (Just (Just x) ::)) [ joinMaybe . map distribListMaybe . distribListMaybe
                                     , distribListMaybe . map joinMaybe]
      >| Cong (distribListMaybe .) [map joinMaybe . (Just (Just x) ::)
                                   , (Just x::)  . map joinMaybe ]
      >| Cong (. map joinMaybe) [distribListMaybe . (Just x ::)
                               , map (x ::) . distribListMaybe]
      >| Nil

    in app ? ? (runProof steps
               [ funExt $ maybeFunctorCompose ? ?
               , Refl
               , sym $ funExt $ maybeFunctorCompose ? ?
               , sym $ funExt $ doubleDistCommutes x
               , funExt $ \v => Refl
               , funExt $ \ys => assert_total (pentagon1 ys )
               , Refl
               , Refl
               , Refl
               , Refl]) xs


joinConsNil : {0 a : Type} -> (ls : Maybe (List (List a))) -> map joinList (map ([] ::) ls) === map joinList ls
joinConsNil Nothing = Refl
joinConsNil (Just []) = Refl
joinConsNil (Just (x :: xs)) = Refl

joinListMaybeBind :
   {0 a : Type} ->
   (v : Maybe (List a)) ->
   (w : List a -> Maybe (List (List a))) ->
   map joinList (maybeBind v w) === maybeBind v (map joinList . w)
joinListMaybeBind Nothing w = Refl
joinListMaybeBind (Just x) w = Refl

%unbound_implicits on
whu : {0 a : Type} -> {y : a} ->
      {xs : Maybe (List a)} ->
      {zs : Maybe (List a)} ->
      maybeBind (map (y ::) xs) (\z => map (z ++) zs)
    = map (y ::) (maybeBind xs (\z => map (z ++) zs))
whu {xs = Nothing} {zs} = Refl
whu {xs = (Just x)} {zs} = sym (maybeFunctorCompose (Prelude.(::) y) (x ++) zs)

%unbound_implicits off
0
ConsAppend : {0 a : Type} ->
   (x : List (List a)) ->
   (w : List a) ->
   joinList (w :: x) = w ++ joinList x
ConsAppend x w = Refl

0
joinListConsAppend : {0 a : Type} ->
   (v : Maybe (List (List a))) ->
   (w : List a)->
   map joinList (map (w ::) v) === map (w ++) (map joinList v)
joinListConsAppend Nothing w = Refl
joinListConsAppend (Just x) w = cong Just (ConsAppend x w)

lemmadistribBind :  {0 a : Type} ->
    (xs : (List (Maybe a), List (Maybe a))) ->
    uncurry maybeBind (bimap id (flip (\y => map (y ++))) (bimap distribListMaybe distribListMaybe xs)) = distribListMaybe (uncurry (++) xs)
lemmadistribBind ([], z) = maybeFunctorId (distribListMaybe z)
lemmadistribBind ((Nothing :: xs), z) = Refl
lemmadistribBind (((Just y) :: xs), z) with (lemmadistribBind (xs, z))
  _ | pat = trans whu (cong (map (y::)) pat)

lemma : {0 a : Type} -> (x : a) ->
        (xs : (List (Maybe a), List (Maybe a))) ->
        uncurry maybeBind (bimap id (flip (\y => map (y ++))) (bimap distribListMaybe distribListMaybe (bimap ( Just x ::) id xs)))
          === distribListMaybe (uncurry (++) (bimap (Just x ::) id xs))
lemma x xs = lemmadistribBind (bimap (Just x::) id xs)

0
bimapSwap : {0 a, a', b, b' : Type} ->
            (f : a -> a') -> (g : b -> b') ->
            bimap {f = Pair} id f . bimap {f = Pair} g id === bimap {f = Pair} g id . bimap {f = Pair} id f
bimapSwap f g = funExt $ \(x, y) => Refl

0
pentagon2 : {0 a : Type} -> (ls : List (List (Maybe a))) ->
            map joinList (distribListMaybe (map distribListMaybe ls)) = distribListMaybe (joinList ls)
pentagon2 [] = Refl
pentagon2 ([] :: xs) with (pentagon2 xs)
  pentagon2 ([] :: xs) | ppf = trans (joinConsNil ?) ppf
pentagon2 ((Nothing :: ys) :: xs) = Refl
pentagon2 (((Just x) :: ys) :: xs) =
  let fn, gn : (List (Maybe a), List (List (Maybe a))) -> Maybe (List a)
      fn = map (x ::) . distribListMaybe . uncurry (++) . bimap id joinList
      gn = map joinList . uncurry maybeBind . bimap (map (x ::) . distribListMaybe) (flip (\v => map (v ::))) . bimap id distribListMaybe . bimap id (map distribListMaybe)

      steps : CongPipeline 29 ((List (Maybe a), List (List (Maybe a))) -> Maybe (List a))
      steps = Cong (map joinList . uncurry maybeBind .)
                   (AddNest (bimap (map (x ::) . distribListMaybe) (flip (\v => map (v ::))) .)
                       [ bimap id distribListMaybe . bimap id (map distribListMaybe)
                       , bimap id (distribListMaybe . map distribListMaybe)]
                   (AddNest (. bimap id (distribListMaybe . map distribListMaybe))
                      [ bimap (map (x ::) . distribListMaybe) (flip (\v => map (v ::)))
                      , bimap id (flip (\v => map (v ::))) . bimap (map (x ::) . distribListMaybe) id]
                   (AddNest (\vx => bimap id (flip (\v => map (v ::))) . vx . bimap id (distribListMaybe . map distribListMaybe))
                      [ bimap (map (x ::) . distribListMaybe) id
                      , bimap (map (x ::)) id . bimap distribListMaybe id] Nil)))
           >| Cong (. bimap id (flip (\v => map (v ::))) . bimap (map (x ::)) id . bimap distribListMaybe id . bimap id (distribListMaybe . map distribListMaybe))
                    [map joinList . uncurry maybeBind
                    , uncurry maybeBind . bimap id (map joinList .)]
           >| AddNest (uncurry maybeBind .)
                (AddNest (. bimap (map (x ::)) id . bimap distribListMaybe id . bimap id (distribListMaybe . map distribListMaybe))
                     ( bimap id (map joinList .) . bimap id (flip (\v => map (v ::)))
                     :: AddNest (bimap id)
                         [ (map joinList .) . flip (\v => map (v ::))
                         , flip (\v => map (v ++)) . map joinList] Nil)
                (AddNest (bimap id (flip (\v => map (v ++))) .)
                     (AddNest (. bimap id (distribListMaybe . map distribListMaybe) )
                         (AddNest (. bimap distribListMaybe id)
                             [ bimap id (map joinList) . bimap (map (x ::)) id
                             , bimap (map (x ::)) id . bimap id (map joinList) ]
                         (AddNest (bimap (map (x ::)) id . )
                            [bimap id (map joinList) . bimap distribListMaybe id
                           , bimap distribListMaybe id . bimap id (map joinList) ] Nil))
                     (AddNest (bimap (map (x ::)) id . bimap distribListMaybe id .)
                          [ bimap id (map joinList) . bimap id (distribListMaybe . map distribListMaybe)
                          , bimap id (map joinList . distribListMaybe . map distribListMaybe)]
                     (AddNest (. bimap id (map joinList . distribListMaybe . map distribListMaybe))
                        [ bimap (map (x ::)) id . bimap distribListMaybe id
                        , bimap (map (x ::) . distribListMaybe) id
                        , bimap (distribListMaybe . (Just x::)) id]
                      (AddNest (bimap distribListMaybe id . bimap (Just x ::) id .)
                         (AddNest (bimap id)
                               [ (map joinList . distribListMaybe . map distribListMaybe)
                               , (distribListMaybe . joinList)] Nil) Nil)))
                    ) Nil
                ))
           (uncurry maybeBind . bimap id (flip (\v => map (v ++))) . bimap distribListMaybe id . bimap (Just x ::) id . bimap id distribListMaybe . bimap id joinList
           :: (AddNest (. bimap id joinList)
                 (AddNest (uncurry maybeBind . bimap id (flip (\v => map (v ++))) .)
                     (AddNest (bimap distribListMaybe id .)
                         [ bimap (Just x ::) id . bimap id distribListMaybe
                         , bimap id distribListMaybe . bimap (Just x ::) id]
                     (AddNest (. bimap (Just x ::) id)
                       [ bimap distribListMaybe id . bimap id distribListMaybe
                       , bimap distribListMaybe distribListMaybe ] Nil)
                    )
                   [distribListMaybe . uncurry (++) . bimap (Just x ::) id
                   , map (x ::) . distribListMaybe . uncurry (++)])
               Nil))
      0 prf : gn === fn
      prf = runProof steps
        (funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => joinListMaybeBind v w)
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\v => funExt $ \w => joinListConsAppend v w)
        :: funExt (\(v, w) => Refl)
        :: bimapSwap ? ?
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\v => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\v => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (assert_total pentagon2)
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (\(v, w) => Refl)
        :: funExt (lemma x)
        :: funExt (\(v, w) => Refl)
        :: Nil
        )
  in app ? ? prf (ys, xs)

triangle1 :
    {0 a : Type} -> (x : List a) ->
    Just x === distribListMaybe (mapImpl Just x)
triangle1 [] = Refl
triangle1 (x :: xs) = rewrite sym (triangle1 xs) in Refl

public export
listMaybeDistrib : SetDistrib ListIsMonad MaybeIsMonad
listMaybeDistrib = MkDistribProof
  (MkNT (\_ => distribListMaybe)
    (\x, y, m  => funExt $ \z => sym $ ListMaybe.square m z)
  )
  (\_ => pentagon1)
  (\_ => pentagon2)
  (\_ => triangle1)
  (\_ => \case Nothing => Refl
               (Just x) => Refl)

