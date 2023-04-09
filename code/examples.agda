module examples where

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

infix 25 _+_

infix 20 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

id : (A : Set) → A → A
id A x = x

id' : {A : Set} → A → A
id' x = x
