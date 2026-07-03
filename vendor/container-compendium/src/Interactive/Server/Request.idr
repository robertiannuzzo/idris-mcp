module Interactive.Server.Request

public export
data Method
  = GET
  | POST
  | PUT
  | PATCH
  | UPDATE
  | DELETE

export
Show Method where
  show GET = "GET"
  show POST = "POST"
  show PUT = "PUT"
  show PATCH = "PATCH"
  show UPDATE = "UPDATE"
  show DELETE = "DELETE"

export
Eq Method where
  GET == GET = True
  POST == POST = True
  PUT == PUT = True
  PATCH == PATCH = True
  UPDATE == UPDATE = True
  DELETE == DELETE = True
  _ == _ = False

public export
data HTTPVersion : Type where
  V1991 : HTTPVersion
  V1996 : HTTPVersion
  V1997 : HTTPVersion
  V2015 : HTTPVersion
  V2020 : HTTPVersion

revision : HTTPVersion -> (Nat, Nat)
revision V1991 = (0, 9)
revision V1996 = (1, 0)
revision V1997 = (1, 1)
revision V2015 = (2, 0)
revision V2020 = (3, 0)

public export
record Request where
  constructor MkReq
  method : Method
  version : HTTPVersion
  headers : List (String, String)
  path : String
  body : String

