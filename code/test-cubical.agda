{-# OPTIONS --cubical #-}

open import satslogik
open import Cubical.HITs.SetQuotients.Base


B : {ctxt} → Set
B {Γ} = Formula / _⊢_∼_ Γ


-- Define ⋀ ⋁ ¬ ⊤ ⊥

{-

Properties of a Boolean algebra

  Commutativity:     x ⋁ y = y ⋁ x                        x ⋀ y = y ⋀ x
  Associativity:     x ⋁ (y ⋁ z) = (x ⋁ y) ⋁ z           x ⋀ (y ⋀ z) = (x ⋀ y) ⋀ z
  Absorbtion:        y ⋁ (x ⋀ y) = y                      y ⋀ (x ⋁ y) = y
  Distributivity:    x ⋁ (y ⋀ z) = (x ⋁ y) ⋀ (x ⋁ z)     x ⋀ (y ⋁ z) = (x ⋀ y) ⋁ (x ⋀ z)
  Complements:       x ⋁ ¬x = ⊤                           x ⋀ ¬x = ⊥
  (Identity:         x ⋁ ⊥ = x                            x ⋀ ⊤ = x)

-}


{-

Structure: ⟨ B, ⋀, ⋁, ¬, ⊤/1, ⊥/0 ⟩

Every Boolean algebra is a distributive lattice ⟨ L, ≤ ⟩ where x,y ∈ L
has infimum x ⋀ y and supremum x ⋁ y

    x ≤ y   iff   x ⋀ y = x   iff   x ⋁ y = y

Show ⟨ B, ≤ ⟩ Boolean.

-}
