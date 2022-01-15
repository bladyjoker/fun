{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module LIVector where

import GHC (Type)

data Nat where
    Zero :: Nat
    Succ :: Nat -> Nat

type family Add (l :: Nat) (r :: Nat) where
    Add Zero r = r
    Add (Succ l) r = Succ (Add l r)

type Vector :: Nat -> * -> *
data Vector :: Nat -> * -> * where
    Nil :: Vector 'Zero a
    Cons :: a -> Vector l a -> Vector ( 'Succ l) a

-- length :: Vector l a -> l
-- length = _

append :: Vector ll a -> Vector lr a -> Vector (Add ll lr) a
append Nil vr = vr
append (Cons x xs) vr = Cons x (xs `append` vr)
