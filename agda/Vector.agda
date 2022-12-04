module Vector where

open import Nat
open import Agda.Primitive\

variable
 A : Set
 m n : Nat

data Vector (A : Set) : Nat → Set where
  vnil : Vector A z
  vcons : (x : A) → Vector A m → Vector A (s m)

append : Vector A m → Vector A n → Vector A (m + n)
append vnil x₁ = x₁
append (vcons x x₂) x₁ = vcons x (append x₂ x₁)

data _≡_ {A : Set l} : (x : A) → A → Set (s l) where
  refl : (x : A) → x ≡ x

≡-comm : { A : Set } {x y : A} → x ≡ y → y ≡ x
≡-comm (refl x) = refl x

≡-cong : { A B : Set } {x y : A} (f : A → B) → x ≡ y → (f x) ≡ (f y)
≡-cong f (refl x) =  refl (f x)

≡-trans : { A : Set } {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans (refl x) (refl x) = refl x

test : {a b : Set} → a ≡ b → a → b
test (refl x) x = x

reverse'a : Vector A (s m + n) → Vector A (m + s n)
reverse'a v = test +-shift-s v

reverse' : Vector A m → Vector A n → Vector A (m + n)
reverse' vnil ys = ys
reverse' (vcons x xs) ys = reverse'a (reverse' xs (vcons x ys))
