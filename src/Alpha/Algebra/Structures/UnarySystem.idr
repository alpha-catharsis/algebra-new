---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.UnarySystem

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Data.TH

---------------
-- Unary system
---------------

public export
interface UnarySystem t a where
  unOpTH : TH t -> a -> a

public export
unOp : UnarySystem t a => a -> a
unOp = unOpTH (MkTH {t})

-----------------------
-- Default unary system
-----------------------

public export
interface DefaultUnarySystem a where
  defaultUnarySystem : TH a -> Type

public export
unOp' : DefaultUnarySystem a => UnarySystem (defaultUnarySystem (MkTH a)) a => a -> a
unOp' = unOpTH (MkTH (defaultUnarySystem (MkTH a)))
