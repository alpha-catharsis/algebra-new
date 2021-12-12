---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.Semigroup

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Structures.Magma

------------------
-- Semigroup Proof
------------------

public export
0 AssociativePrf : {a : Type} -> Magma t a -> Type
AssociativePrf (MkMagma _ f) = (x : a) -> (y : a) -> (z : a) -> f x (f y z) = f (f x y) z

------------
-- Semigroup
------------

public export
data Semigroup : Type -> Type -> Type where
  [noHints]
  MkSemigroup : (0 t : Type) -> (mgm : Magma t a) -> (0 prf : AssociativePrf mgm) -> Semigroup t a

public export
0 semigroupType : Semigroup t a => Type
semigroupType @{MkSemigroup t _ _} = t

public export
semigroupMagma : Semigroup t a => Magma t a
semigroupMagma @{MkSemigroup _ mgm _} = mgm

public export
0 semigroupPrf : (sg : Semigroup t a) => AssociativePrf (semigroupMagma @{sg})
semigroupPrf @{MkSemigroup _ _ prf} = prf

--------------------
-- Default semigroup
--------------------

public export
data DefaultSemigroup : Type -> Type where
  [noHints]
  MkDefaultSemigroup : (0 t : Type) -> (0 a : Type) -> DefaultSemigroup a

public export
0 defaultSemigroup : DefaultSemigroup a => Type
defaultSemigroup @{MkDefaultSemigroup t _} = t

