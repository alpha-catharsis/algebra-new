---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Data.Nat

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Data.Ops
import Alpha.Algebra.Structures.Pointed
import Alpha.Algebra.Structures.UnarySystem

----------------------------
-- Pointed set implementions
----------------------------

public export
%hint
pointedAddNat : PointedG Add Nat
pointedAddNat = MkPointedG Add Z

public export
%hint
pointedMultNat : PointedG Mult Nat
pointedMultNat = MkPointedG Mult (S Z)

public export
%hint
basepointNat : Pointed Nat
basepointNat = MkPointed pointedAddNat

----------------------------
-- UnarySystem implementions
----------------------------

public export
%hint
unarySystemSuccNat : UnarySystemG Succ Nat
unarySystemSuccNat = MkUnarySystemG Succ S

public export
%hint
unarySystemNat : UnarySystem Nat
unarySystemNat = MkUnarySystem unarySystemSuccNat
