module Main

import Alpha.Algebra

-- test : (dp : DefaultPointed a) => Pointed (defaultPointed @{dp}) a => a
-- test = basepoint'

-- test2 : Pointed Add a => Monoid Add a => a
-- test2 = basepoint {t=Add}

-- public export
-- data Semigroup2 : (t : Type) -> (a : Type) -> Type where
--   [noHints]
--   MkSemigroup2 : (0 t : Type) -> (mgm : Magma t a) => (0 prf : AssociativePrf mgm) -> Semigroup2 t a

-- test3 : Semigroup2 Add a => a -> a -> a
-- test3 @{MkSemigroup2 _ _} x y = binOp {t=Add} x y

-- -- public export
-- -- data Pointed : Type -> Type -> Type where
-- --   [noHints]
-- --   MkPointed : (0 t : Type) -> a -> Pointed t a

-- record TypeHolder where
--   constructor MkTypeHolder
--   type : Type

-- interface Pointed2 (0 t : TypeHolder) (0 a : Type) where
--   basepoint2 : t -> a


main : IO ()
main = do
  putStrLn "\nOK"
