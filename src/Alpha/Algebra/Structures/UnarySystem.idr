---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.UnarySystem

--------------------------
-- Generalized UnarySystem
--------------------------

public export
data UnarySystemG : Type -> Type -> Type where
  [noHints]
  MkUnarySystemG : (t : Type) -> (a -> a) -> UnarySystemG t a

public export
unOpG : UnarySystemG t a => a -> a
unOpG @{MkUnarySystemG _ f} = f

--------------
-- UnarySystem
--------------

public export
data UnarySystem : Type -> Type where
  [noHints]
  MkUnarySystem : UnarySystemG t a -> UnarySystem a

public export
unOp : UnarySystem a => a -> a
unOp @{MkUnarySystem g} = unOpG @{g}
