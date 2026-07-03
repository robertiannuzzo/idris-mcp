module Interactive.Server.Response

import Interactive.Server.Serialise

public export
record Response where
  constructor MkResponse
  version : String
  status : String
  headers : List (String, String)
  body : String

Encode Response where
  encode r = r.status ++ r.body
