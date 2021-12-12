---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Data.Nat

-------------------
-- External imports
-------------------

import Data.Nat

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Data.Ops
import Alpha.Algebra.Data.TH
import Alpha.Algebra.Structures.Magma
import Alpha.Algebra.Structures.Monoid
import Alpha.Algebra.Structures.Pointed
import Alpha.Algebra.Structures.Semigroup
import Alpha.Algebra.Structures.UnarySystem

----------------------------
-- Pointed set implementions
----------------------------

public export
Pointed Add Nat where
  basepointTH _ = Z

public export
Pointed Mult Nat where
  basepointTH _ = (S Z)

public export
DefaultPointed Nat where
  defaultPointed _ = Add

----------------------------
-- UnarySystem implementions
----------------------------

public export
UnarySystem Add Nat where
  unOpTH _ = S

public export
DefaultUnarySystem Nat where
  defaultUnarySystem _ = Add

----------------------
-- Magma implementions
----------------------

public export
Magma Add Nat where
  binOpTH _ = plus

public export
Magma Mult Nat where
  binOpTH _ = mult

public export
DefaultMagma Nat where
  defaultMagma _ = Add

--------------------------
-- Semigroup implementions
--------------------------

public export
Associative Add Nat where
  associativePrf = plusAssociative

public export
Semigroup.Semigroup Add Nat where

public export
Associative Mult Nat where
  associativePrf = multAssociative

public export
Semigroup.Semigroup Mult Nat where

public export
DefaultSemigroup Nat where
  defaultSemigroup _ = Add

-----------------------
-- Monoid implementions
-----------------------

public export
LeftIdentElem Add Nat where
  leftIdentPrf = plusZeroLeftNeutral

public export
RightIdentElem Add Nat where
  rightIdentPrf = plusZeroRightNeutral

public export
IdentElem Add Nat where

public export
Monoid.Monoid Add Nat where

public export
DefaultMonoid Nat where
  defaultMonoid _ = Add
