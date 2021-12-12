---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Structures.Pointed

--------------
-- Pointed Set
--------------

public export
data Pointed : Type -> Type -> Type where
  [noHints]
  MkPointed : (0 t : Type) -> a -> Pointed t a

public export
0 pointedType : Pointed t a => Type
pointedType @{MkPointed t _} = t

public export
basepoint : Pointed t a => a
basepoint @{MkPointed _ x} = x

----------------------
-- Default pointed Set
----------------------

public export
data DefaultPointed : Type -> Type where
  [noHints]
  MkDefaultPointed : (0 t : Type) -> (0 a : Type) -> DefaultPointed a

public export
0 defaultPointed : DefaultPointed a => Type
defaultPointed @{MkDefaultPointed t _} = t

public export
basepoint' : (dp : DefaultPointed a) => Pointed (defaultPointed @{dp}) a => a
basepoint' @{MkDefaultPointed t _ } = basepoint {t}
