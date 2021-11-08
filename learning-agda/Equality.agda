module Equality where

data _≡_ {A : Set} : (x : A) → A → Set where
  refl : (x : A) → x ≡ x

≡-comm : { A : Set } {x y : A} → x ≡ y → y ≡ x
≡-comm (refl x) = refl x

≡-cong : { A B : Set } {x y : A} (f : A → B) → x ≡ y → (f x) ≡ (f y)
≡-cong f (refl x) =  refl (f x)

≡-trans : { A : Set } {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans (refl x) (refl x) = refl x

≡-cong-app : { A B : Set} {f g : A -> B} → f ≡ g → (x : A) → f x ≡ g x
≡-cong-app (refl f) x = refl (f x)

≡-subst : { A : Set } { x y : A } ( P : A → Set ) → x ≡ y → P x → P y -- TODO: Why not P x ≡ P y?
≡-subst pred (refl x) prop = prop
