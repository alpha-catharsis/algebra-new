---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.Pointed

--------------------------
-- Generalized Pointed Set
--------------------------

public export
data PointedG : Type -> Type -> Type where
  [noHints]
  MkPointedG : (t : Type) -> a -> PointedG t a

public export
basepointG : PointedG t a => a
basepointG @{MkPointedG _ x} = x

--------------
-- Pointed Set
--------------

public export
data Pointed : Type -> Type where
  [noHints]
  MkPointed : PointedG t a -> Pointed a

public export
basepoint : Pointed a => a
basepoint @{MkPointed g} = basepointG @{g}
