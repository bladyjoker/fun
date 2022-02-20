module Vector where

open import  Nat

data Vector (A : Set) : Nat -> Set where
  vnil : Vector A z
  vcons : { l : Nat } (x : A) -> Vector A l -> Vector A (s l)
