module Nat where

open import Equality

data Nat : Set where
  z : Nat
  s : Nat → Nat

-- # Addition
_+_ : Nat → Nat → Nat
z + y = y
s x + y = s (x + y)

+z : (m : Nat) → (m + z) ≡ m
+z z = refl z
+z (s m) = ≡-cong s (+z m)

+z-comm : (m : Nat) → m ≡ (m + z)
+z-comm m = ≡-comm (+z m)

z+ : (m : Nat) → (z + m) ≡ m
z+ m = refl m

z+-comm : (m : Nat) → m ≡ (z + m)
z+-comm m = ≡-comm (z+ m)

+-shift-s : (m n : Nat) → (s m + n) ≡ (m + s n)
+-shift-s z n = refl (s n)
+-shift-s (s m) n = ≡-cong s (+-shift-s m n)

s+right : (m n : Nat) → s (m + n) ≡ (m + s n)
s+right = +-shift-s

s+left : (m n : Nat) → s (m + n) ≡ (s m + n)
s+left m n = refl (s (m + n))

+-comm : (m n : Nat) → (m + n) ≡ (n + m)
+-comm z n = ≡-comm (+z n)
+-comm (s m) n = ≡-trans (≡-cong s (+-comm m n)) (+-shift-s n m)

+-comm-z : (m : Nat) → (m + z) ≡ (z + m)
+-comm-z m = +-comm m z

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

+'-shift-s : (m n : Nat) → (s m +' n) ≡ (m +' s n)
+'-shift-s z n = refl (s n)
+'-shift-s (s m) n = refl (m +' s (s n))

+'-shift-s' : (m n : Nat) → (m +' s n) ≡ (s m +' n)
+'-shift-s' m n = ≡-comm (+'-shift-s m n)

s+' : (m n : Nat) → s (m +' n) ≡ (s m +' n)
s+' z n = refl (s n)
s+' (s m) n = s+' m (s n)

+'-id-r : (m : Nat) → (m +' z) ≡ m
+'-id-r z = refl z
+'-id-r (s m) = ≡-trans (≡-comm (s+' m z)) (≡-cong s (+'-id-r m))

+'-id-l : (m : Nat) → (z +' m) ≡ m
+'-id-l m = refl m

+'-comm-zero : (m : Nat) → (m +' z) ≡ (z +' m)
+'-comm-zero = +'-id-r

+'-comm : (m n : Nat) → (m +' n) ≡ (n +' m)
+'-comm z n = ≡-comm (+'-id-r n)
+'-comm (s m) n = +'-comm m (s n)

+'-assoc : (m n p : Nat) → ((m +' n) +' p) ≡ (m +' (n +' p))
+'-assoc z n p = refl (n +' p)
+'-assoc (s m) n p = ≡-trans (+'-assoc m (s n) p) (≡-comm (≡-cong (m +'_) (s+' n p)))

+≣+' : (m n : Nat) → (m + n) ≡ (m +' n)
+≣+' z n = refl n
+≣+' (s m) n =  ≡-trans (+-shift-s m n) (+≣+' m (s n))

-- # Multiplication
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

*z : (m : Nat) → (m * z) ≡ z
*z z = refl z
*z (s m) = refl z

z* : (m : Nat) → (z * m) ≡ z
z* z = refl z
z* (s m) = refl z

*sz : (m : Nat) → (m * s z) ≡ m
*sz z = refl z
*sz (s m) = ≡-trans (≡-cong (λ x → s (m + x)) (*z m)) ((≡-cong s (+z m)))

sz* : (m : Nat) → (s z * m) ≡ m
sz* z = refl z
sz* (s m) = ≡-cong s (+z m)

*sz-comm : (m : Nat) → m ≡ (m * s z)
*sz-comm m = ≡-comm (*sz m)

*s : (m n : Nat) → (m * s n) ≡ (m + (m * n))
*s z n = refl z
*s (s m) n = ≡-cong s (≡-trans (+-assocom n m (m * n)) (≡-cong (λ x → m + (n + x)) (*-comm m n)))

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

*-assoc-comm : (m n p : Nat) → ((m * n) * p) ≡ (m * (n * p))
*-assoc-comm m n p = ≡-comm (*-assoc m n p)

-- # Exponentials
_^_ : Nat → Nat → Nat
z ^ z = s z
z ^ s n = z
s m ^ z = s z
s m ^ s n = s m * (s m ^ n)

sz^ : ∀ (n : Nat) → (s z ^ n) ≡ s z
sz^ z = refl (s z)
sz^ (s n) = ≡-trans (≡-cong ((s z ^ n) +_) (*z (s z ^ n))) (≡-trans (+z (s z ^ n)) (sz^ n))

^sz : ∀ (x : Nat) → (x ^ s z) ≡ x
^sz z = refl z
^sz (s x) = ≡-trans (≡-cong (λ b → s (x + b)) (*z x)) (≡-cong s (+z x))

^z : ∀ (n : Nat) → (n ^ z) ≡ s z
^z z = refl (s z)
^z (s n) = refl (s z)

^s : ∀ (x m : Nat) → (x ^ s m) ≡ (x * (x ^ m))
^s z m = refl z
^s (s x) m = refl ((s x ^ m) + ((s x ^ m) * x))

^+ : ∀ (x m n : Nat) → ((x ^ m) * (x ^ n)) ≡ (x ^ (m + n))
^+ z z n = ≡-trans (≡-cong ((z ^ n) +_) (*z (z ^ n))) (+z (z ^ n))
^+ (s x) z n = ≡-trans (≡-cong ((s x ^ n) +_) (*z (s x ^ n))) (+z (s x ^ n))
^+ x (s m) n = ≡-trans (≡-cong (_* (x ^ n))(^s x m)) (≡-trans (*-assoc-comm x (x ^ m) (x ^ n)) (≡-trans (≡-cong (x *_) (^+ x m n)) (≡-comm (^s x (m + n)))))

^+-comm : ∀ (x m n : Nat) → (x ^ (m + n)) ≡ ((x ^ m) * (x ^ n))
^+-comm x m n = ≡-comm (^+ x m n)

-- Ref: https://en.wikipedia.org/wiki/Binomial_theorem
binomial' : ∀ (x y m n : Nat) → Nat
binomial' x y z n = y ^ n
binomial' x y (s m) n = ((x ^ (s m)) * (y ^ n)) + (binomial' x y m (s n))

binomial : ∀ (x y m : Nat) → Nat
binomial x y m = binomial' x y m z

binomial≡binomial' : ∀ (x y m : Nat) → binomial x y m ≡ binomial' x y m z
binomial≡binomial' x y m = refl (binomial' x y m z)

binomial^z : ∀ (x y : Nat) → binomial x y z ≡ s z
binomial^z x y = ≡-trans (binomial≡binomial' x y z) (^z y)

{-# TERMINATING #-}
binomial^s : ∀ (x y m : Nat) → binomial x y (s m) ≡ ((binomial x y (s z)) * (binomial x y m))
binomial^s x y z = ≡-comm (lemma x y)
  where
    lemma : ∀ (x y : Nat) → (binomial x y (s z) * binomial x y z) ≡ (binomial x y (s z))
    lemma x y = ≡-trans (≡-cong ((binomial x y (s z)) *_) (binomial^z x y)) (*sz (binomial x y (s z)))
binomial^s x y (s m) = ≡-comm (lemma x y m)
  where
    lemma : ∀ (x y m : Nat) → (binomial x y (s z) * binomial x y (s m)) ≡ binomial x y (s (s m))
    lemma x y m = ≡-trans (≡-cong (binomial x y (s z) *_) (binomial^s x y m)) (≡-trans (≡-cong ((binomial x y (s z)) *_) (≡-comm (binomial^s x y m))) (≡-comm (binomial^s x y (s m))))

binomial^sz : ∀ (x y : Nat) → binomial x y (s z) ≡ (x + y)
binomial^sz x y = ≡-trans (binomial≡binomial' x y (s z)) (≡-trans (≡-cong (((x ^ s z) * (y ^ z)) +_) (^sz y)) (≡-trans (≡-cong (λ b → (b * (y ^ z)) + y) (^sz x)) (≡-trans (≡-cong (λ b → (x * b) + y) (^z y)) (≡-cong (_+ y) (*sz x)))))

+^s : ∀ (x y m : Nat) → ((x + y) ^ (s m)) ≡ ((x + y) * ((x + y) ^ m))
+^s x y m = ^s (x + y) m

+^≡binomial : ∀ (x y m : Nat) → ((x + y) ^ m) ≡ binomial x y m
+^≡binomial x y z = ≡-trans (^z (x + y)) (≡-comm (binomial^z x y))
+^≡binomial x y (s m) = ≡-trans (^s (x + y) m) (≡-comm (lemma x y m))
  where
    lemma : ∀ (x y m : Nat) → binomial x y (s m) ≡ ((x + y) * ((x + y) ^ m))
    lemma x y m = ≡-trans (binomial^s x y m) (≡-trans (≡-cong (_* (binomial x y m)) (binomial^sz x y)) (≡-cong ((x + y) *_) (≡-comm (+^≡binomial x y m))))

*^ : ∀ (x y m : Nat) → ((x * y) ^ m) ≡ ((x ^ m) * (y ^ m))
*^ x y z = ≡-trans (^z (x * y)) (≡-comm (lemma x y))
  where
    lemma : ∀ (x y : Nat) → ((x ^ z) * (y ^ z)) ≡ s z
    lemma x y = ≡-trans (≡-cong (_* (y ^ z)) (^z x)) (≡-trans (≡-cong ((y ^ z) +_) (*z (y ^ z))) (≡-cong (_+ z) (^z y)))
*^ x y (s m) = ≡-trans (^s (x * y) m) (≡-trans (≡-cong ((x * y) *_) (*^ x y m)) (≡-comm (lemma x y m)))
  where
    lemma : ∀ (x y m : Nat) → ((x ^ s m) * (y ^ s m)) ≡ ((x * y) * ((x ^ m) * (y ^ m)))
    lemma x y m = ≡-trans (≡-cong (_* (y ^ s m)) (^s x m)) (≡-trans (≡-cong ((x * (x ^ m)) *_) (^s y m)) (≡-trans (*-assoc-comm x (x ^ m) (y * (y ^ m))) (≡-trans (≡-cong (x *_) (*-assoc (x ^ m) (y) (y ^ m))) (≡-trans (≡-cong (λ b → x * (b * (y ^ m))) (*-comm (x ^ m) y)) (≡-trans (≡-cong (x *_) (*-assoc-comm y (x ^ m) (y ^ m))) (*-assoc x y ((x ^ m) * (y ^ m))))))))

^^ : ∀ (x m n : Nat) → ((x ^ m) ^ n) ≡ (x ^ (m * n))
^^ x m z = ≡-trans (^z (x ^ m)) (≡-comm (lemma x m))
  where
    lemma : ∀ (x m : Nat) → (x ^ (m * z)) ≡ s z
    lemma x m = ≡-trans (≡-cong (x ^_) (*z m)) (^z x)
^^ x m (s n) = ≡-trans (^s (x ^ m) n) (≡-comm (lemma x m n))
  where
    lemma : ∀ (x m n : Nat) → (x ^ (m * s n)) ≡ ((x ^ m) * ((x ^ m) ^ n))
    lemma x m n = ≡-trans (≡-cong (x ^_) (*s m n) ) (≡-trans (^+-comm x m (m * n)) (≡-cong ((x ^ m) *_) (≡-comm (^^ x m n))))

^* : ∀ (x m n : Nat) → (x ^ (m * n)) ≡ ((x ^ m) ^ n)
^* x m n = ≡-comm (^^ x m n)
