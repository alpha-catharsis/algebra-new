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

----------------
-- Monoid Proofs
----------------

public export
0 MonoidLeftPrf : (t : Type) -> (a : Type) -> Pointed t a => Magma t a => Type
MonoidLeftPrf t a = (x : a) -> binOp {t} (basepoint {t}) x = x

public export
0 MonoidRightPrf : (t : Type) -> (a : Type) -> Pointed t a => Magma t a => Type
MonoidRightPrf t a  = (x : a) -> binOp {t} x (basepoint {t}) = x

---------
-- Monoid
---------

public export
interface Pointed t a => Semigroup t a => Monoid t a where
  0 monoidLeftPrfTH : TH t -> MonoidLeftPrf t a
  0 monoidRightPrfTH : TH t -> MonoidRightPrf t a

public export
0 monoidLeftPrf : Monoid t a => MonoidLeftPrf t a
monoidLeftPrf = monoidLeftPrfTH (MkTH {t})

public export
0 monoidRightPrf : Monoid t a => MonoidRightPrf t a
monoidRightPrf = monoidRightPrfTH (MkTH {t})

-----------------
-- Default monoid
-----------------

public export
interface DefaultMonoid a where
  defaultMonoid : TH a -> Type

public export
0 monoidLeftPrf' : DefaultMonoid a => Monoid (defaultMonoid (MkTH a)) a =>
                   MonoidLeftPrf (defaultMonoid (MkTH a)) a
monoidLeftPrf' = monoidLeftPrfTH (MkTH (defaultMonoid (MkTH a)))

public export
0 monoidRightPrf' : DefaultMonoid a => Monoid (defaultMonoid (MkTH a)) a =>
                    MonoidRightPrf (defaultMonoid (MkTH a)) a
monoidRightPrf' = monoidRightPrfTH (MkTH (defaultMonoid (MkTH a)))
