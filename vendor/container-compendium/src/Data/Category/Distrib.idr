module Data.Category.Distrib

import Data.Category.NaturalTransformation
import Data.Category.Functor
import Data.Category.Endofunctor
import Data.Category.Monad

%hide Prelude.Functor
%hide Prelude.Ops.infixl.(*>)

record DistributiveLaw
    {0 o1 : Type} {0 c1 : Category o1}
    (endoT : Endo c1)
    (endoS : Endo c1)
    (t : Monad c1 endoT)
    (s : Monad c1 endoS) where
    constructor MkDistrib
    nat : (endoT ⨾⨾ endoS) =>> (endoS ⨾⨾ endoT)

    -- t (s (s x)) ---> s (t (s x0)) ------> s (s (t x))
    --     |                                    |
    --     |                                    |
    --     |                                    |
    --     v                                    v
    --  t (s x) ---------------------------> s (t x)
    0 sq1 : (x : o1) ->
            let 0 tμS : endoT.mapObj ((endoS ⨾⨾ endoS).mapObj x) ~> endoT.mapObj (endoS.mapObj x)
                tμS = endoT.mapHom ((endoS ⨾⨾ endoS).mapObj x)
                                (endoS.mapObj x)
                                (s.mult.component x)
                0 tμS' : (endoT ⨾⨾ (endoS ⨾⨾ endoS)).mapObj x ~> (endoT ⨾⨾ endoS).mapObj x
                tμS' = ?arg tμS
                0 ll : (endoT ⨾⨾ endoS).mapObj x ~> (endoS ⨾⨾ endoT).mapObj x
                ll = nat.component x
            in Type

