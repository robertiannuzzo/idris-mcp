module Data.Category.FunctorHaskell
ListF : Functor Set Set
ListF = MkFunctor
    { mapObj = List
    , mapHom = \_, _ => map
    , presId = \a => funExt listMapId
    , presComp = \a, b, c, f, g => funExt (listMapComp f g)
    }
  where
    listMapId : {a : Type} -> (xs : List a) -> map Basics.id xs === xs
    listMapId [] = Refl
    listMapId (x :: xs) = cong (x ::) (listMapId xs)

    listMapComp : {a, b, c : Type} ->
                  (f : a -> b) -> (g : b -> c) -> (xs : List a) ->
                  map (g . f) xs === map g (map f xs)
    listMapComp f g [] = Refl
    listMapComp f g (x :: xs) = cong (g (f x) ::) (listMapComp f g xs)

MaybeF : Functor Set Set
MaybeF = MkFunctor
    { mapObj = Maybe
    , mapHom = \_, _ => map
    , presId = \_ => funExt $ \case Nothing => Refl
                                    (Just x) => Refl
    , presComp = \_, _, _, f, g => funExt $ \case Nothing => Refl
                                                  (Just x) => Refl
    }
parameters {a, b : Type}

  mapList : (a -> b) -> List a -> List b
  mapList = mapHom ListF a b

  mapMaybe : (a -> b) -> Maybe a -> Maybe b
  mapMaybe = mapHom MaybeF a b
export infix 2 <*!
public export
(<*!) : {0 o1, o2, o3 : Type} -> {0 a : Category o1} -> {0 b : Category o2} -> {0 c : Category o3} ->
      Functor b c -> Functor a b -> Functor a c
(<*!) f g = g ⨾⨾ f
