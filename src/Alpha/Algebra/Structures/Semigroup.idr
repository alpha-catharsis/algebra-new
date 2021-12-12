---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.Semigroup

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Data.TH
import Alpha.Algebra.Structures.Magma

------------------
-- Semigroup Proof
------------------

public export
0 SemigroupPrf : (t : Type) -> (a : Type) -> Magma t a => Type
SemigroupPrf t a = (x : a) -> (y : a) -> (z : a) ->
                   binOp {t} x (binOp {t} y z) = binOp {t} (binOp {t} x y) z

------------
-- Semigroup
------------

public export
interface Magma t a => Semigroup t a where
  0 semigroupPrfTH : TH t -> SemigroupPrf t a

public export
0 semigroupPrf : Semigroup t a => SemigroupPrf t a
semigroupPrf = semigroupPrfTH (MkTH {t})

--------------------
-- Default semigroup
--------------------

public export
interface DefaultSemigroup a where
  defaultSemigroup : TH a -> Type

public export
0 semigroupPrf' : DefaultSemigroup a => Semigroup (defaultSemigroup (MkTH a)) a =>
                  SemigroupPrf (defaultSemigroup (MkTH a)) a
semigroupPrf' = semigroupPrfTH (MkTH (defaultSemigroup (MkTH a)))
