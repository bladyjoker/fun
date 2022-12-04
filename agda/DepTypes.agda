module DepTypes where


data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

infix 2 _+_
infix 3 _*_

_+_ : Nat → Nat → Nat
n + zero = n
n + succ m = succ (n + m)

_*_ : Nat → Nat → Nat
n * zero = zero
n * succ m = n * m + n


f : Nat -> Nat
f x = x + (succ zero)

r = f (succ (succ (succ zero)))



data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

rr : List Nat
rr = zero :: (zero :: [])


data Vect (A : Set) : Nat -> Set where
  empty : Vect A zero
  vcons : {n : Nat} -> A -> Vect A n -> Vect A (succ n)


inner : {n : Nat} -> Vect Nat n -> Vect Nat n -> Nat
inner {zero} vl vr = zero
inner {succ n} (vcons x xs) (vcons y ys) = x * y + inner {n} xs ys

rrr = vcons (succ (succ zero)) empty

rrrr = inner rrr rrr

append : {A : Set} {n m : Nat} -> Vect A n -> Vect A m -> Vect A (m + n)
append {_} empty vr = vr
append (vcons x vl) vr = vcons x (append vl vr)


Proposition = Set

data Absurd : Proposition where
data Truth : Proposition where
  tt : Truth

data _Or_ (A B : Proposition) : Proposition where
  inL : A -> A Or B
  inR : B -> A Or B

data _And_ (A B : Proposition) : Proposition where
  _,_ : A -> B -> A And B

data _Implies_ (A  B : Proposition) : Proposition where
  _==>_ : A -> B -> A Implies B

ff : {A B : Proposition} -> A -> B -> A Or B
ff x y = inR y

data Bool : Set where
  true : Bool
  false : Bool


_≤_ : Nat → Nat → Bool
zero ≤ n = true
succ n ≤ zero = false
succ n ≤ succ m = n ≤ m

True : Bool → Proposition
True true = Truth
True false = Absurd

data SList : Nat -> Set where
  sempty : SList zero
  scons : {n : Nat} (m : Nat) -> {True (n ≤ m)} -> SList n -> SList m

rrrrr = scons (succ zero) {tt} sempty

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

Fin : Nat → Proposition
Fin zero = Truth
Fin (succ n) = Fin n

_LE_ : Nat -> Nat -> Set
zero LE y = Truth
succ x LE zero = Absurd
succ x LE succ y = x LE y

data Even : Nat → Set where
  evenZero : Even zero
  evenSucc : {m : Nat} → Even m → Even (succ (succ m))

testEven : Even (succ (succ (succ (succ zero))))
testEven = evenSucc (evenSucc evenZero)

_∘_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
fL ∘ fR =  λ x → fR (fL x)

data _IsAncestorOf_ : {A : Set} (a d : A) → Set where
  _isParentOf_ : {A : Set} (a d : A) → a IsAncestorOf d
  isAncestorOf : {A : Set} {a b c : A} → a IsAncestorOf b → b IsAncestorOf c → a IsAncestorOf c

data Person : Set where
  slavka : Person
  drazen : Person
  zoran : Person
  nenad : Person
  zdravka : Person

ipo = slavka isParentOf drazen
ipo1 = zoran isParentOf drazen
ipo2 = zdravka isParentOf slavka
ipo3 = zdravka isParentOf zoran

anc : zdravka IsAncestorOf drazen
anc = isAncestorOf (zdravka isParentOf slavka) (slavka isParentOf drazen)

