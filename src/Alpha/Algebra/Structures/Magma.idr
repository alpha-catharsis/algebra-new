---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.Magma

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Data.TH

--------
-- Magma
--------

public export
interface Magma t a where
  binOpTH : TH t -> a -> a -> a

public export
binOp : Magma t a => a -> a -> a
binOp = binOpTH (MkTH {t})

----------------
-- Default magma
----------------

public export
interface DefaultMagma a where
  defaultMagma : TH a -> Type

public export
binOp' : DefaultMagma a => Magma (defaultMagma (MkTH a)) a => a -> a -> a
binOp' = binOpTH (MkTH (defaultMagma (MkTH a)))
