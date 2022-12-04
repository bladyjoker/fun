module Bool where

open import Equality

data 𝔹 : Set where
  t : 𝔹
  f : 𝔹

_&&_ : 𝔹 → 𝔹 → 𝔹
t && n = n
f && _ = f

&&-idem : (m : 𝔹) → (m && m) ≡ m
&&-idem t = refl t
&&-idem f = refl f

&&-assoc : (m n p : 𝔹) → ((m && n) && p) ≡ (m && (n && p))
&&-assoc t n p = refl (n && p)
&&-assoc f n p = refl f

&&-comm : (m n : 𝔹) → (m && n) ≡ (n && m)
&&-comm t t = refl t
&&-comm t f = refl f
&&-comm f t = refl f
&&-comm f f = refl f

_||_ : 𝔹 → 𝔹 → 𝔹
t || _ = t
f || b = b

||-idem : (m : 𝔹) → (m || m) ≡ m
||-idem t = refl t
||-idem f = refl f

||-assoc : (m n p : 𝔹) → ((m || n) || p) ≡ (m || (n || p))
||-assoc t n p = refl t
||-assoc f n p = refl (n || p)

||-comm : (m n : 𝔹) → (m || n) ≡ (n || m)
||-comm t t = refl t
||-comm t f = refl t
||-comm f t = refl t
||-comm f f = refl f

&&-dist|| : (m n p : 𝔹) → (m && (n || p)) ≡ ((m && n) || (m && p))
&&-dist|| t n p = refl (n || p)
&&-dist|| f n p = refl f

~_ : 𝔹 → 𝔹
~ t = f
~ f = t

~~=id : (b : 𝔹) → (~ ~ b) ≡ b
~~=id t = refl t
~~=id f = refl f

demorgan1 : (m n : 𝔹) → (~ (m || n)) ≡ ((~ m) && (~ n))
demorgan1 t n = refl f
demorgan1 f n = refl (~ n)

demorgan2 : (m n : 𝔹) → (~ (m && n)) ≡ ((~ m) || (~ n))
demorgan2 t n = refl (~ n)
demorgan2 f n = refl t

_⇒_ : 𝔹 → 𝔹 → 𝔹
t ⇒ y = y
f ⇒ y = t

material-implication : (m n : 𝔹) → (m ⇒ n) ≡ ((~ m) || n)
material-implication t n = refl n
material-implication f n = refl t

transposition : (m n : 𝔹) → (m ⇒ n) ≡ ((~ n) ⇒ (~ m))
transposition t t = refl t
transposition t f = refl f
transposition f t = refl t
transposition f f = refl t

if_then_else : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if t then x else _ = x
if f then _ else y = y


{-
# References

- Propositional calculus https://en.wikipedia.org/wiki/Propositional_calculus
-}

