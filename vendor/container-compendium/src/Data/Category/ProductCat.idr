module Data.Category.ProductCat

import Data.Category
import Data.Category.Functor
import Data.Category.Product
public export
(×) : Category o -> Category p -> Category (o * p)
(×) x y = MkCategory
  (\a, b => ((~:>) x a.π1 b.π1) * ((~:>) y a.π2 b.π2))
  (\v => x.id v.π1 && y.id v.π2)
  (\f, g => (|:>) x f.π1 g.π1 && (|:>) y f.π2 g.π2)
  (\_, _, idl => cong2 (&&)
      (x.idRight _ _ idl.π1)
      (y.idRight _ _ idl.π2) `trans` Data.Product.projIdentity idl
  )
  (\_, _, idr => cong2 (&&)
      (x.idLeft  _ _ idr.π1)
      (y.idLeft  _ _ idr.π2) `trans` Data.Product.projIdentity idr
  )
  (\_, _, _, _, f, g, h => cong2 (&&)
      (compAssoc x _ _ _ _ f.π1 g.π1 h.π1)
      (compAssoc y _ _ _ _ f.π2 g.π2 h.π2)
  )
