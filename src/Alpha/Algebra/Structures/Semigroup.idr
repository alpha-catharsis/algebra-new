---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.Semigroup

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Data.TH
import Alpha.Algebra.Structures.Magma

------------
-- Semigroup
------------

public export
interface Magma t a => Associative t a => Semigroup t a where

--------------------
-- Default Semigroup
--------------------

public export
interface DefaultSemigroup a where
  defaultSemigroup : TH a -> Type
