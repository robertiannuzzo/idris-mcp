module Interactive.Commands

import Data.Container


World : Type
World = Container

data IOCommand : Type where
  Write : String -> IOCommand
  Read : IOCommand

Response : IOCommand -> Type
Response (Write x) = Unit
Response (Read) = String


IOWorld : World
IOWorld = (!>) IOCommand Response

data DepIO : World -> Type -> Type where
  Leaf : a -> DepIO w a
  Do : (c : w.req) -> (p : w.res c -> DepIO w a) -> DepIO w a

(>>=) : (c : w.req) -> (p : w.res c -> DepIO w a) -> DepIO w a
(>>=) = Do

(>>) : (c : w.req) -> (DepIO w a) -> DepIO w a
(>>) a b = a >>= const b

pure : a -> DepIO w a
pure = Leaf

func : DepIO IOWorld Bool
func = do Write "password :"
          "bob" <- Read
          | _ => Write "login incorrect"
                 >> pure False
          pure True

