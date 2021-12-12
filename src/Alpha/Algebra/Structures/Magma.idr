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

-----------------
-- Magma morphism
-----------------

public export
interface Magma t a => Magma t' b => MagmaMorphism t t' a b (0 f : a -> b) where
  magmaMorphismPrf : (x : a) -> (y : a) -> f (binOp {t} x y) = binOp {t=t'} (f x) (f y)

-------------
-- Free magma
-------------

public export
data FreeMagmaOp : Type where

public export
data FreeMagma : Type -> Type where
  MagmaElem : a -> FreeMagma a
  MagmaOp : FreeMagma a -> FreeMagma a -> FreeMagma a

public export
Magma FreeMagmaOp (FreeMagma a) where
  binOpTH _ = MagmaOp

public export
DefaultMagma (FreeMagma a) where
  defaultMagma _ = FreeMagmaOp

-----------------------
-- Free magma extension
-----------------------

public export
freeMagmaExtension : Magma t b => (a -> b) -> (FreeMagma a -> b)
freeMagmaExtension f (MagmaElem x) = f x
freeMagmaExtension f (MagmaOp lm rm) = binOp {t} (freeMagmaExtension {t} f lm) (freeMagmaExtension {t} f rm)

public export
{0 f : a -> b} -> Magma t b => MagmaMorphism FreeMagmaOp t (FreeMagma a) b (freeMagmaExtension {t} f) where
  magmaMorphismPrf _ _ = Refl
