---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Data.TH

--------------
-- Type holder
--------------

public export
data TH : Type -> Type where
  MkTH : (0 t : Type) -> TH t

public export
0 type : TH t -> Type
type (MkTH t) = t
