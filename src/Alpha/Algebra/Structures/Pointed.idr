---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.Pointed

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Data.TH

--------------
-- Pointed set
--------------

public export
interface Pointed t a where
  basepointTH : TH t -> a

public export
basepoint : Pointed t a => a
basepoint = basepointTH (MkTH {t})

----------------------
-- Default pointed Set
----------------------

public export
interface DefaultPointed a where
  defaultPointed : TH a -> Type

public export
basepoint' : DefaultPointed a => Pointed (defaultPointed (MkTH a)) a => a
basepoint' = basepointTH (MkTH (defaultPointed (MkTH a)))

--------------
-- Pointed map
--------------

public export
interface Pointed t a => Pointed t' b => PointedMap t t' a b (0 f : a -> b) where
  pointedMapPrf : f (basepointTH (MkTH t)) = basepointTH (MkTH t')
