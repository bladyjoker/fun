module List where

open import Equality
open import Nat

data List (A : Set) : Set where
  [] : List A
  _::_ : (x  : A) -> List A -> List A

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

++-id-r : {A : Set} (xs : List A) → (xs ++ []) ≡ xs
++-id-r [] = refl []
++-id-r (x :: xs) = ≡-cong (x ::_) (++-id-r xs)

++-id-r' : {A : Set} (xs : List A) → xs ≡ (xs ++ [])
++-id-r' xs = ≡-comm (++-id-r xs)

++-id-l : {A : Set} (xs : List A) → ([] ++ xs) ≡ xs
++-id-l xs = refl xs

++-id-comm : {A : Set} (xs : List A) → (xs ++ []) ≡ ([] ++ xs)
++-id-comm [] = refl []
++-id-comm (x :: xs) = ≡-cong (x ::_) (++-id-comm xs)

++-assoc : {A : Set} (xs ys zs : List A) → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
++-assoc [] ys zs =  refl (ys ++ zs)
++-assoc (x :: xs) ys zs =  ≡-cong (x ::_) (++-assoc xs ys zs)

reverse' : {A : Set} → List A → List A → List A
reverse' [] ys = ys
reverse' (x :: xs) ys = reverse' xs (x :: ys)

reverse : {A : Set} → List A → List A
reverse xs = reverse' xs []

rev'rev'=id : {A : Set} (xs ys : List A) → reverse' (reverse' xs ys) [] ≡ reverse' ys xs
rev'rev'=id [] ys =  refl (reverse' (ys) [])
rev'rev'=id (x :: xs)  ys = rev'rev'=id xs (x :: ys)

rev-lemma1 : {A : Set} (xs ys : List A) → reverse' xs ys ≡ (reverse' xs [] ++ ys)
rev-lemma1 [] ys = refl ys
rev-lemma1 (x :: xs) [] = ++-id-r' (reverse' xs (x :: []))
rev-lemma1 (x :: xs) (y :: ys) = ≡-comm (≡-trans (≡-cong (_++ (y :: ys)) (rev-lemma1 xs (x :: []))) (≡-trans (++-assoc (reverse' xs []) (x :: []) (y :: ys)) (≡-comm (rev-lemma1 xs (x :: (y :: ys))))))

genrev'rev'=id : {A : Set} (xs ys zs : List A) → reverse' (reverse' xs ys) zs ≡ (reverse' ys xs ++ zs)
genrev'rev'=id xs ys [] = ≡-trans (rev'rev'=id xs ys) (++-id-r' (reverse' ys xs))
genrev'rev'=id xs ys (x :: zs) = ≡-trans (rev-lemma1 (reverse' xs ys) (x :: zs)) (≡-cong (_++ (x :: zs)) (rev'rev'=id xs ys))

revrev=id : {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
revrev=id xs = rev'rev'=id xs []

length : {A : Set} → List A → Nat
length [] = z
length (x :: xs) = s (length xs)

++-distlen : {A : Set} (xs ys : List A) → (length xs + length ys) ≡ (length (xs ++ ys))
++-distlen [] ys = refl (length ys)
++-distlen (x :: xs) ys = ≡-cong s (++-distlen xs ys)
