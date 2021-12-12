---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.Magma

--------
-- Magma
--------

public export
data Magma : Type -> Type -> Type where
  [noHints]
  MkMagma : (0 t : Type) -> (a -> a -> a) -> Magma t a

public export
0 magmaType : Magma t a => Type
magmaType @{MkMagma t _} = t

public export
binOp : Magma t a => a -> a -> a
binOp @{MkMagma _ f} = f

----------------
-- Default magma
----------------

public export
data DefaultMagma : Type -> Type where
  [noHints]
  MkDefaultMagma : (0 t : Type) -> (0 a : Type) -> DefaultMagma a

public export
0 defaultMagma : DefaultMagma a => Type
defaultMagma @{MkDefaultMagma t _} = t

public export
binOp' : (dp : DefaultMagma a) => Magma (defaultMagma @{dp}) a => a -> a -> a
binOp' @{MkDefaultMagma t _ } = binOp {t}
