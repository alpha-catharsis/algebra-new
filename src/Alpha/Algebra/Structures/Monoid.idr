---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.Monoid

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Data.TH
import Alpha.Algebra.Structures.Magma
import Alpha.Algebra.Structures.Pointed
import Alpha.Algebra.Structures.Semigroup

---------
-- Monoid
---------

public export
interface Semigroup t a => IdentElem t a => Monoid t a where

-----------------
-- Default monoid
-----------------

public export
interface DefaultMonoid a where
  defaultMonoid : TH a -> Type
