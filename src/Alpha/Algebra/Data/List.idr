---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Data.List

-------------------
-- External imports
-------------------

import Data.List

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Data.Ops
import Alpha.Algebra.Data.TH
import Alpha.Algebra.Structures.Magma
import Alpha.Algebra.Structures.Monoid
import Alpha.Algebra.Structures.Pointed
import Alpha.Algebra.Structures.Semigroup

----------------------------
-- Pointed set implementions
----------------------------

public export
Pointed Append (List a) where
  basepointTH _ = []

public export
DefaultPointed (List a) where
  defaultPointed _ = Append

----------------------
-- Magma implementions
----------------------

public export
Magma Append (List a) where
  binOpTH _ = (++)

public export
DefaultMagma (List a) where
  defaultMagma _ = Append

--------------------------
-- Semigroup implementions
--------------------------

public export
Associative Append (List a) where
  associativePrf = appendAssociative

public export
Semigroup.Semigroup Append (List a) where

public export
DefaultSemigroup (List a) where
  defaultSemigroup _ = Append

-----------------------
-- Monoid implementions
-----------------------

appendNilLeftNeutral : (l : List a) -> [] ++ l = l
appendNilLeftNeutral _ = Refl

public export
Monoid.Monoid Append (List a) where
  monoidLeftPrfTH _ = appendNilLeftNeutral
  monoidRightPrfTH _ = appendNilRightNeutral

public export
DefaultMonoid (List a) where
  defaultMonoid _ = Append
