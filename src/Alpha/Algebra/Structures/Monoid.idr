---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.Monoid

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Structures.Magma
import Alpha.Algebra.Structures.Pointed
import Alpha.Algebra.Structures.Semigroup

----------------
-- Monoid Proofs
----------------

public export
MonoidLeftPrf : {a : Type} -> Pointed t a -> Magma t a -> Type
MonoidLeftPrf (MkPointed _ u) (MkMagma _ f) = (x : a) -> f u x = x

public export
MonoidRightPrf : {a : Type} -> Pointed t a -> Magma t a -> Type
MonoidRightPrf (MkPointed _ u) (MkMagma _ f) = (x : a) -> f x u = x

---------
-- Monoid
---------

public export
data Monoid : Type -> Type -> Type where
  [noHints]
  MkMonoid : (0 t : Type) -> (pnt : Pointed t a) -> (sg : Semigroup t a) ->
             MonoidLeftPrf pnt (semigroupMagma @{sg}) ->
             MonoidRightPrf pnt (semigroupMagma @{sg}) -> Monoid t a


public export
0 monoidType : Monoid t a => Type
monoidType @{MkMonoid t _ _ _ _} = t

public export
monoidPointed : Monoid t a => Pointed t a
monoidPointed @{MkMonoid _ pnt _ _ _} = pnt

public export
monoidSemigroup : Monoid t a => Semigroup t a
monoidSemigroup @{MkMonoid _ _ sg _ _} = sg

public export
0 monoidLeftPrf : (mn : Monoid t a) => MonoidLeftPrf (monoidPointed @{mn}) (semigroupMagma @{monoidSemigroup @{mn}})
monoidLeftPrf @{MkMonoid _ _ _ lprf _} = lprf

public export
0 monoidRightPrf : (mn : Monoid t a) => MonoidRightPrf (monoidPointed @{mn}) (semigroupMagma @{monoidSemigroup @{mn}})
monoidRightPrf @{MkMonoid _ _ _ _ rprf} = rprf

-----------------
-- Default monoid
-----------------

public export
data DefaultMonoid : Type -> Type where
  [noHints]
  MkDefaultMonoid : (0 t : Type) -> (0 a : Type) -> DefaultMonoid a

public export
0 defaultMonoid : DefaultMonoid a => Type
defaultMonoid @{MkDefaultMonoid t _} = t
