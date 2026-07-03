module Interactive.Server.Serialise

public export
interface Encode t where
  encode : t -> String

export
Encode String where
  encode = id

export
Encode Int where
  encode = show

public export
interface Decode t where
  decode : String -> Maybe t

export
Decode String where
  decode = Just
