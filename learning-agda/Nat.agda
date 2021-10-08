module Nat where

open import Equality

data Nat : Set where
  z : Nat
  s : Nat → Nat

_+_ : Nat → Nat → Nat
z + y = y
s x + y = s (x + y)

+-id-r : (m : Nat) → (m + z) ≡ m
+-id-r z = refl z
+-id-r (s m) = ≡-cong s (+-id-r m)

+-id-r' : (m : Nat) → m ≡ (m + z)
+-id-r' m = ≡-comm (+-id-r m)

+-id-l : (m : Nat) → (z + m) ≡ m
+-id-l m = refl m

+-id-l' : (m : Nat) → m ≡ (z + m)
+-id-l' m = ≡-comm (+-id-l m)

+-comm-zero : (m : Nat) → (m + z) ≡ (z + m)
+-comm-zero z = refl z
+-comm-zero (s m) = ≡-cong s (+-comm-zero m)

+-lemma2 : (m n : Nat) → (s m + n) ≡ (m + s n)
+-lemma2 z n = refl (s n)
+-lemma2 (s m) n = ≡-cong s (+-lemma2 m n)

+-lemma1 : (m n : Nat) → s (m + n) ≡ (m + s n)
+-lemma1 = +-lemma2

+-lemma0 : (m n : Nat) → s (m + n) ≡ (s m + n)
+-lemma0 m n = refl (s (m + n))

+-comm : (m n : Nat) → (m + n) ≡ (n + m)
+-comm z n = ≡-comm (+-id-r n)
+-comm (s m) n = ≡-trans (≡-cong s (+-comm m n)) (+-lemma2 n m)

+-assoc : (m n p : Nat) → ((m + n) + p) ≡ (m + (n + p))
+-assoc z n p = refl (n + p)
+-assoc (s m) n p = ≡-cong s (+-assoc m n p)

+-assoc' : (m n p : Nat) → (m + (n + p)) ≡ ((m + n) + p)
+-assoc' m n p = ≡-comm (+-assoc m n p)

+-assocom : (m n p : Nat) → (m + (n + p)) ≡ (n + (m + p))
+-assocom m n p = ≡-trans (+-assoc' m n p) (≡-trans (≡-cong (_+ p) (+-comm m n)) (+-assoc n m p))

_+'_ : Nat → Nat → Nat
z +' y = y
s x +' y = x +' s y

+'-lemma1 : (m n : Nat) → (s m +' n) ≡ (m +' s n)
+'-lemma1 z n = refl (s n)
+'-lemma1 (s m) n = refl (m +' s (s n))

+'-lemma2 : (m n : Nat) → (m +' s n) ≡ (s m +' n)
+'-lemma2 m n = ≡-comm (+'-lemma1 m n)

+'-lemma3 : (m n : Nat) → s (m +' n) ≡ (s m +' n)
+'-lemma3 z n = refl (s n)
+'-lemma3 (s m) n = +'-lemma3 m (s n)

+'-id-r : (m : Nat) → (m +' z) ≡ m
+'-id-r z = refl z
+'-id-r (s m) = ≡-trans (≡-comm (+'-lemma3 m z)) (≡-cong s (+'-id-r m))

+'-id-l : (m : Nat) → (z +' m) ≡ m
+'-id-l m = refl m

+'-comm-zero : (m : Nat) → (m +' z) ≡ (z +' m)
+'-comm-zero = +'-id-r

+'-comm : (m n : Nat) → (m +' n) ≡ (n +' m)
+'-comm z n = ≡-comm (+'-id-r n)
+'-comm (s m) n = +'-comm m (s n)

+'-assoc : (m n p : Nat) → ((m +' n) +' p) ≡ (m +' (n +' p))
+'-assoc z n p = refl (n +' p)
+'-assoc (s m) n p = ≡-trans (+'-assoc m (s n) p) (≡-comm (≡-cong (m +'_) (+'-lemma3 n p)))

+≣+' : (m n : Nat) → (m + n) ≡ (m +' n)
+≣+' z n = refl n
+≣+' (s m) n =  ≡-trans (+-lemma2 m n) (+≣+' m (s n))

_*_ : Nat → Nat → Nat
z * n = z
s m * n = n + (n * m) -- alternating multiplication was the key!

_*'_ : Nat → Nat → Nat
z *' n = z
s m *' n = n + (m * n)


*-comm : (m n : Nat) → (m * n) ≡ (n * m)
*-comm z z = refl z
*-comm z (s n) = refl z
*-comm (s m) z = refl z
*-comm (s m) (s n) = ≡-cong s (≡-trans (+-assocom n m (m * n)) (≡-cong (λ x → m + (n + x)) (*-comm m n)))

*-zero-r : (m : Nat) → (m * z) ≡ z
*-zero-r z = refl z
*-zero-r (s m) = refl z

*-zero-l : (m : Nat) → (z * m) ≡ z
*-zero-l z = refl z
*-zero-l (s m) = refl z

*-id-r : (m : Nat) → (m * s z) ≡ m
*-id-r z = refl z
*-id-r (s m) = ≡-trans (≡-cong (λ x → s (m + x)) (*-zero-r m)) ((≡-cong s (+-id-r m)))

*-id-l : (m : Nat) → (s z * m) ≡ m
*-id-l z = refl z
*-id-l (s m) = ≡-cong s (+-id-r m)

*-id-r' : (m : Nat) → m ≡ (m * s z)
*-id-r' m = ≡-comm (*-id-r m)

*-lemma1 : (m n : Nat) → (m * s n) ≡ (m + (m * n))
*-lemma1 z n = refl z
*-lemma1 (s m) n = ≡-cong s (≡-trans (+-assocom n m (m * n)) (≡-cong (λ x → m + (n + x)) (*-comm m n)))

*≣*' : (m n : Nat) → (m * n) ≡ (m *' n)
*≣*' z n = refl z
*≣*' (s m) n = ≡-cong (n +_) (*-comm n m)


*-dist+ : (m n p : Nat) → ((m * n) + (m * p)) ≡ (m * (n + p))
*-dist+ z n p = refl z
*-dist+ (s m) n p = ≡-trans (+-assoc n (n * m) (p + (p * m))) (≡-trans (≡-cong (n +_) (+-assoc' (n * m) p (p * m))) (≡-trans (≡-cong (λ x → n + (x + (p * m))) (+-comm (n * m) p)) (≡-trans (≡-cong (n +_) (+-assoc p (n * m) (p * m))) (≡-trans (+-assoc' n p ((n * m) + (p * m))) (≡-cong ((n + p) +_) (*-dist+' m n p))))))
  where
    *-dist+' : (m n p : Nat) →  ((n * m) + (p * m)) ≡ ((n + p) * m)
    *-dist+' m n p = ≡-trans (≡-cong (_+ (p * m)) (*-comm n m)) (≡-trans (≡-cong ((m * n) +_) (*-comm p m)) (≡-trans (*-dist+ m n p) (*-comm m (n + p))))

*-dist+' : (m n p : Nat) →  ((n * m) + (p * m)) ≡ ((n + p) * m)
*-dist+' m n p = ≡-trans (≡-cong (_+ (p * m)) (*-comm n m)) (≡-trans (≡-cong ((m * n) +_) (*-comm p m)) (≡-trans (*-dist+ m n p) (*-comm m (n + p))))

*-assoc : (m n p : Nat) → (m * (n * p)) ≡ ((m * n) * p)
*-assoc z n p = refl z
*-assoc (s m) n p = ≡-trans (≡-cong ((n * p) +_ ) ((*-assoc' n p m))) (≡-trans (≡-cong (λ x → (n * p) + (n * x)) (*-comm p m)) (≡-trans (≡-cong (λ x → (n * p) + x) (*-assoc n m p)) (*-dist+' p n (n * m))))
  where
    *-assoc' : (m n p : Nat) → ((m * n) * p) ≡ (m * (n * p))
    *-assoc' m n p = ≡-comm (*-assoc m n p)

*-assoc' : (m n p : Nat) → ((m * n) * p) ≡ (m * (n * p))
*-assoc' m n p = ≡-comm (*-assoc m n p)


_^_ : Nat → Nat → Nat
z ^ z = s z
z ^ s n = z
s m ^ z = s z
s m ^ s n = s m * (s m ^ n)

^-const : ∀ (n : Nat) → (s z ^ n) ≡ s z
^-const z = refl (s z)
^-const (s n) = ≡-trans (≡-cong ((s z ^ n) +_) (*-zero-r (s z ^ n))) (≡-trans (+-id-r (s z ^ n)) (^-const n))

^-lemma1 : ∀ (x m : Nat) → (x ^ s m) ≡ (x * (x ^ m))
^-lemma1 z m = refl z
^-lemma1 (s x) m = refl ((s x ^ m) + ((s x ^ m) * x))

^-+exponent' : ∀ (x m n : Nat) → ((x ^ m) * (x ^ n)) ≡ (x ^ (m + n))
^-+exponent' z z n = ≡-trans (≡-cong ((z ^ n) +_) (*-zero-r (z ^ n))) (+-id-r (z ^ n))
^-+exponent' (s x) z n = ≡-trans (≡-cong ((s x ^ n) +_) (*-zero-r (s x ^ n))) (+-id-r (s x ^ n))
^-+exponent' x (s m) n = ≡-trans (≡-cong (_* (x ^ n))(^-lemma1 x m)) (≡-trans (*-assoc' x (x ^ m) (x ^ n)) (≡-trans (≡-cong (x *_) (^-+exponent' x m n)) (≡-comm (^-lemma1 x (m + n)))))

^-+exponent : ∀ (x m n : Nat) → (x ^ (m + n)) ≡ ((x ^ m) * (x ^ n))
^-+exponent x m n = ≡-comm (^-+exponent' x m n)

^-*exponent : ∀ (x m n : Nat) → (x ^ (m * n)) ≡ ((x ^ m) ^ n)
^-*exponent x m n = {!!}

^-powof+ : ∀ (x y m : Nat) → ((x + y) ^ m) ≡ ((x ^ m) * (y ^ m))
^-powof+ x y m = {!!}

^-powof* : ∀ (x y m : Nat) → ((x * y) ^ m) ≡ ((x ^ m) * (y ^ m))
^-powof* x y m = {!!}

^-powof^ : ∀ (x m n : Nat) → ((x ^ m) ^ n) ≡ (x ^ (m * n))
^-powof^ x m n = {!!}
