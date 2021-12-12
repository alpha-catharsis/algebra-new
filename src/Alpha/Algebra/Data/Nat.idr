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
import Alpha.Algebra.Structures.Magma
import Alpha.Algebra.Structures.Monoid
import Alpha.Algebra.Structures.Pointed
import Alpha.Algebra.Structures.Semigroup
import Alpha.Algebra.Structures.UnarySystem

----------------------------
-- Pointed set implementions
----------------------------

public export
%hint
pointedAddNat : Pointed Add Nat
pointedAddNat = MkPointed Add Z

public export
%hint
pointedMultNat : Pointed Mult Nat
pointedMultNat = MkPointed Mult (S Z)

public export
%hint
defaultPointedNat : DefaultPointed Nat
defaultPointedNat = MkDefaultPointed Add Nat

----------------------------
-- UnarySystem implementions
----------------------------

public export
%hint
unarySystemSuccNat : UnarySystem Succ Nat
unarySystemSuccNat = MkUnarySystem Succ S

public export
%hint
defaultUnarySystemNat : DefaultUnarySystem Nat
defaultUnarySystemNat = MkDefaultUnarySystem Succ Nat

----------------------
-- Magma implementions
----------------------

public export
%hint
magmaAddNat : Magma Add Nat
magmaAddNat = MkMagma Add (+)

public export
%hint
magmaMultNat : Magma Mult Nat
magmaMultNat = MkMagma Mult (*)

public export
%hint
defaultMagmaNat : DefaultMagma Nat
defaultMagmaNat = MkDefaultMagma Add Nat

--------------------------
-- Semigroup implementions
--------------------------

public export
%hint
semigroupAddNat : Semigroup Add Nat
semigroupAddNat = MkSemigroup Add magmaAddNat plusAssociative

public export
%hint
semigroupMultNat : Semigroup Mult Nat
semigroupMultNat = MkSemigroup Mult magmaMultNat multAssociative

-----------------------
-- Monoid implementions
-----------------------

public export
%hint
monoidAddNat : Monoid Add Nat
monoidAddNat = MkMonoid Add pointedAddNat semigroupAddNat plusZeroLeftNeutral plusZeroRightNeutral

public export
%hint
monoidMultNat : Monoid Mult Nat
monoidMultNat = MkMonoid Mult pointedMultNat semigroupMultNat multOneLeftNeutral multOneRightNeutral

public export
%hint
defaultMonoidNat : DefaultMonoid Nat
defaultMonoidNat = MkDefaultMonoid Add Nat
