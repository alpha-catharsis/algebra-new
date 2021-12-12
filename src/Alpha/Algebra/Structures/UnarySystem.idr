---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.UnarySystem

---------------
-- Unary system
---------------

public export
data UnarySystem : Type -> Type -> Type where
  [noHints]
  MkUnarySystem : (0 t : Type) -> (a -> a) -> UnarySystem t a

public export
0 unarySystemType : UnarySystem t a => Type
unarySystemType @{MkUnarySystem t _} = t

public export
unOp : UnarySystem t a => a -> a
unOp @{MkUnarySystem _ f} = f

-----------------------
-- Default unary system
-----------------------

public export
data DefaultUnarySystem : Type -> Type where
  [noHints]
  MkDefaultUnarySystem : (0 t : Type) -> (0 a : Type) -> DefaultUnarySystem a

public export
0 defaultUnarySystem : DefaultUnarySystem a => Type
defaultUnarySystem @{MkDefaultUnarySystem t _} = t

public export
unOp' : (dus : DefaultUnarySystem a) => UnarySystem (defaultUnarySystem @{dus}) a => a -> a
unOp' @{MkDefaultUnarySystem t _} = unOp {t}
