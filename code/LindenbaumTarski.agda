{-# OPTIONS --cubical #-}
module LindenbaumTarski where


open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)

open import Cubical.Relation.Binary.Base

open import Cubical.Data.Nat.Base
open import Cubical.Data.Prod.Base

open import Cubical.Algebra.DistLattice.Base


-- Definition: Formula
data Formula : Type where
  _∧_   : Formula → Formula → Formula
  _∨_   : Formula → Formula → Formula
  ¬_    : Formula → Formula
  const : ℕ      → Formula
  ⊥     : Formula
  ⊤     : Formula


infix  35  _∧_
infix  30  _∨_
infixl 36  ¬_
infix  20  _⊢_
infix  23  _∶_
 

-- Definition: Context
data ctxt : Type where
  ∅    : ctxt
  _∶_  : ctxt → Formula → ctxt


-- Definition: Lookup
data _∈_ : Formula → ctxt → Type where
  Z  : ∀ {Γ ϕ}   → ϕ ∈ Γ ∶ ϕ
  S  : ∀ {Γ ϕ ψ} → ϕ ∈ Γ → ϕ ∈ Γ ∶ ψ


-- {-# NO_POSITIVITY_CHECK #-}

-- Definition: Provability
data _⊢_ : ctxt → Formula → Type where
  ∧-I : {Γ : ctxt} {ϕ ψ : Formula}
      → Γ ⊢ ϕ
      → Γ ⊢ ψ
      → Γ ⊢ ϕ ∧ ψ
  ∧-E₁ : {Γ : ctxt} {ϕ ψ : Formula}
       → Γ ⊢ ϕ ∧ ψ
       → Γ ⊢ ϕ
  ∧-E₂ : {Γ : ctxt} {ϕ ψ : Formula}
       → Γ ⊢ ϕ ∧ ψ
       → Γ ⊢ ψ
  
  ∨-I₁ : {Γ : ctxt} {ϕ ψ : Formula}
       → Γ ⊢ ψ
       → Γ ⊢ ϕ ∨ ψ
  ∨-I₂ : {Γ : ctxt} {ϕ ψ : Formula}
       → Γ ⊢ ϕ
       → Γ ⊢ ϕ ∨ ψ
  ∨-E : {Γ : ctxt} {ϕ ψ γ : Formula}
      → Γ ⊢ ϕ ∨ ψ
      → Γ ∶ ϕ ⊢ γ
      → Γ ∶ ψ ⊢ γ
      → Γ ⊢ γ
--  ∨-E : {Γ : ctxt} {ϕ ψ γ : Formula}
--      → Γ ⊢ ϕ ∨ ψ
--      → (Γ ⊢ ϕ → Γ ⊢ γ)
--      → (Γ ⊢ ψ → Γ ⊢ γ)
--      → Γ ⊢ γ

  ¬-I : {Γ : ctxt} {ϕ : Formula}
      → Γ ∶ ϕ ⊢ ⊥
      → Γ ⊢ ¬ ϕ
--  ¬-I : {Γ : ctxt} {ϕ : Formula}
--      → (Γ ⊢ ϕ → Γ ⊢ ⊥)
--      → Γ ⊢ ¬ ϕ
  ¬-E : {Γ : ctxt} {ϕ : Formula}
      → Γ ⊢ ϕ
      → Γ ⊢ ¬ ϕ
      → Γ ⊢ ⊥
  
  ⊥-E : {Γ : ctxt} {ϕ : Formula}
      → Γ ⊢ ⊥
      → Γ ⊢ ϕ  
  
  ⊤-I : ∅ ⊢ ⊤
  
  axiom : {Γ : ctxt} {ϕ : Formula}
        → ϕ ∈ Γ
        → Γ ⊢ ϕ
        
  LEM : {Γ : ctxt} {ϕ : Formula}
      → Γ ⊢ ϕ ∨ ¬ ϕ
  
  weakening : {Γ : ctxt} {ϕ ψ : Formula}
            → Γ ⊢ ψ
            → Γ ∶ ϕ ⊢ ψ
  exchange : {Γ : ctxt} {ϕ ψ γ : Formula}
           → (Γ ∶ ϕ) ∶ ψ ⊢ γ
           → (Γ ∶ ψ) ∶ ϕ ⊢ γ
--  contraction : {Γ : ctxt} {ϕ ψ : Formula} → ((Γ ∶ ϕ) ∶ ϕ) ⊢ ψ → (Γ ∶ ϕ) ⊢ ψ


module _ {Γ : ctxt} where

  infixl 25 ¬/_

  ----------------------------------------
  -- Properties of propositional calculus
  ----------------------------------------

  -- Commutativity on ∧
  ∧-comm : ∀ {ϕ ψ : Formula} → Γ ∶ ϕ ∧ ψ ⊢ ψ ∧ ϕ
  ∧-comm = ∧-I (∧-E₂ (axiom Z)) (∧-E₁ (axiom Z))
--  ∧-comm : ∀ {ϕ ψ : Formula} → Γ ⊢ ϕ ∧ ψ → Γ ⊢ ψ ∧ ϕ
--  ∧-comm x = ∧-I (∧-E₂ x) (∧-E₁ x)

  -- Commutativity on ∨
  ∨-comm : {ϕ ψ : Formula} → Γ ∶ ϕ ∨ ψ ⊢ ψ ∨ ϕ
  ∨-comm = ∨-E (axiom Z) (∨-I₁ (axiom Z)) (∨-I₂ (axiom Z))
--  ∨-comm : {ϕ ψ : Formula} → Γ ⊢ ϕ ∨ ψ → Γ ⊢ ψ ∨ ϕ
--  ∨-comm x = ∨-E x ∨-I₁ ∨-I₂


  -- Associativity on ∧
  ∧-assoc1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∧ (ψ ∧ γ) ⊢ (ϕ ∧ ψ) ∧ γ
  ∧-assoc1 = ∧-I (∧-I (∧-E₁ (axiom Z))
                      (∧-E₁ (∧-E₂ (axiom Z))))
                 (∧-E₂ (∧-E₂ (axiom Z)))
--  ∧-assoc1 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∧ (ψ ∧ γ) → Γ ⊢ (ϕ ∧ ψ) ∧ γ
--  ∧-assoc1 x = ∧-I (∧-I (∧-E₁ x) (∧-E₁ (∧-E₂ x)))
--                       (∧-E₂ (∧-E₂ x))
                       
  ∧-assoc2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∧ ψ) ∧ γ ⊢ ϕ ∧ (ψ ∧ γ)
  ∧-assoc2 = ∧-I (∧-E₁ (∧-E₁ (axiom Z)))
                 (∧-I (∧-E₂ (∧-E₁ (axiom Z)))
                      (∧-E₂ (axiom Z)))
--  ∧-assoc2 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ∧ ψ) ∧ γ → Γ ⊢ ϕ ∧ (ψ ∧ γ)
--  ∧-assoc2 x = ∧-I (∧-E₁ (∧-E₁ x))
--                       (∧-I (∧-E₂ (∧-E₁ x)) (∧-E₂ x))

  -- Associativity on ∨
  ∨-assoc1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∨ (ψ ∨ γ) ⊢ (ϕ ∨ ψ) ∨ γ
  ∨-assoc1 = ∨-E (axiom Z)
                 (∨-I₂ (∨-I₂ (axiom Z)))
                 (∨-E (axiom Z)
                      (∨-I₂ (∨-I₁ (axiom Z)))
                      (∨-I₁ (axiom Z)))
--  ∨-assoc1 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∨ (ψ ∨ γ) → Γ ⊢ (ϕ ∨ ψ) ∨ γ
--  ∨-assoc1 x = ∨-E x (λ y → ∨-I₂ (∨-I₂ y))
--                         λ y → ∨-E y (λ z → ∨-I₂ (∨-I₁ z)) ∨-I₁
                                          
  ∨-assoc2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∨ ψ) ∨ γ ⊢ ϕ ∨ (ψ ∨ γ)
  ∨-assoc2 = ∨-E (axiom Z)
                 (∨-E (axiom Z)
                      (∨-I₂ (axiom Z))
                      (∨-I₁ (∨-I₂ (axiom Z))))
                 (∨-I₁ (∨-I₁ (axiom Z)))
--  ∨-assoc2 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ∨ ψ) ∨ γ → Γ ⊢ ϕ ∨ (ψ ∨ γ)
--  ∨-assoc2 x = ∨-E x (λ y → ∨-E y ∨-I₂ λ z → ∨-I₁ (∨-I₂ z)) λ y → ∨-I₁ (∨-I₁ y)


  -- Distributivity over ∧
  ∧-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∧ (ψ ∨ γ) ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  ∧-dist1 = ∨-E (∧-E₂ (axiom Z))
                (∨-I₂ (∧-I (weakening (∧-E₁ (axiom Z))) (axiom Z)))
                (∨-I₁ (∧-I (weakening (∧-E₁ (axiom Z))) (axiom Z)))
--  ∧-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∧ (ψ ∨ γ) → Γ ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
--  ∧-dist1 x = ∨-E (∧-E₂ x) (λ y → ∨-I₂ (∧-I (∧-E₁ x) y))
--                              λ y → ∨-I₁ (∧-I (∧-E₁ x) y)

  ∧-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∧ ψ) ∨ (ϕ ∧ γ) ⊢ ϕ ∧ (ψ ∨ γ)
  ∧-dist2 = ∧-I (∨-E (axiom Z)
                     (∧-E₁ (axiom Z))
                     (∧-E₁ (axiom Z)))
                (∨-E (axiom Z)
                     (∨-I₂ (∧-E₂ (axiom Z)))
                     (∨-I₁ (∧-E₂ (axiom Z))))
--  ∧-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ) → Γ ⊢ ϕ ∧ (ψ ∨ γ)
--  ∧-dist2 x = ∧-I (∨-E x ∧-E₁ ∧-E₁)
--                      (∨-E x (λ y → ∨-I₂ (∧-E₂ y))
--                              λ y → ∨-I₁ (∧-E₂ y))

  -- Distributivity over ∨
  ∨-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∨ (ψ ∧ γ) ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  ∨-dist1 = ∨-E (axiom Z)
                (∧-I (∨-I₂ (axiom Z))
                     (∨-I₂ (axiom Z)))
                (∧-I (∨-I₁ (∧-E₁ (axiom Z)))
                     (∨-I₁ (∧-E₂ (axiom Z))))
--  ∨-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∨ (ψ ∧ γ) → Γ ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
--  ∨-dist1 x = ∨-E x (λ y → ∧-I (∨-I₂ y) (∨-I₂ y))
--                     λ y → ∧-I (∨-I₁ (∧-E₁ y)) (∨-I₁ (∧-E₂ y))
  
  ∨-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∨ ψ) ∧ (ϕ ∨ γ) ⊢ ϕ ∨ (ψ ∧ γ)
  ∨-dist2 = ∨-E (∧-E₁ (axiom Z))
                (∨-I₂ (axiom Z))
                (∨-E (∧-E₂ (weakening (axiom Z)))
                     (∨-I₂ (axiom Z))
                     (∨-I₁ (∧-I (weakening (axiom Z)) (axiom Z))))
--  ∨-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ) → Γ ⊢ ϕ ∨ (ψ ∧ γ)
--  ∨-dist2 x = ∨-E (∧-E₁ x) ∨-I₂ λ y → ∨-E (∧-E₂ x) ∨-I₂  λ z → ∨-I₁ (∧-I y z)


  ------------------------------------------------------
  -- Defining relation where two formulas are related
  -- if they are provably equivalent. Then proving that
  -- the relation is an equivalence relation by proving
  -- it is reflexive, symmetric and transitive.
  ------------------------------------------------------  
  _∼_ : Formula → Formula → Type
  ϕ ∼ ψ = Γ ∶ ϕ ⊢ ψ × Γ ∶ ψ ⊢ ϕ
--  _∼_ : Formula → Formula → Type
--  ϕ ∼ ψ = (Γ ⊢ ϕ → Γ ⊢ ψ) × (Γ ⊢ ψ → Γ ⊢ ϕ)

  ∼-refl : ∀ (ϕ : Formula) → ϕ ∼ ϕ
  ∼-refl _ = axiom Z , (axiom Z)
--  ∼-refl : ∀ (ϕ : Formula) → ϕ ∼ ϕ
--  ∼-refl _ = (λ x → x) , (λ x → x)
  
  ∼-sym : ∀ {ϕ ψ : Formula} → ϕ ∼ ψ → ψ ∼ ϕ
  ∼-sym (A , B) = B , A

  ⊢trans : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ⊢ γ → Γ ∶ γ ⊢ ψ → Γ ∶ ϕ ⊢ ψ
  ⊢trans A B = ∨-E (∨-I₂ A) (exchange (weakening B)) (axiom Z)
--  ⊢trans : ∀ {ϕ ψ γ : Formula} → (Γ ⊢ ϕ → Γ ⊢ ψ) → (Γ ⊢ ψ → Γ ⊢ γ) → (Γ ⊢ ϕ → Γ ⊢ γ)
--  ⊢trans x y z = y (x z)
  
  ∼-trans : ∀ {ϕ ψ γ : Formula} → ϕ ∼ γ → γ ∼ ψ → ϕ ∼ ψ
  ∼-trans x y = ⊢trans (proj₁ x) (proj₁ y) , ⊢trans (proj₂ y) (proj₂ x)



  comm-eq-∧ : ∀ {ϕ ψ : Formula} → ϕ ∧ ψ ∼ ψ ∧ ϕ
  comm-eq-∧ = ∧-comm , ∧-comm

  comm-eq-∨ : ∀ {ϕ ψ : Formula} → ϕ ∨ ψ ∼ ψ ∨ ϕ
  comm-eq-∨ = ∨-comm , ∨-comm

  ass-eq-∧ : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∧ γ) ∼ (ϕ ∧ ψ) ∧ γ
  ass-eq-∧ = ∧-assoc1 , ∧-assoc2

  ass-eq-∨ : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∨ γ) ∼ (ϕ ∨ ψ) ∨ γ
  ass-eq-∨ = ∨-assoc1 , ∨-assoc2

  dist-eq-∧ : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∨ γ) ∼ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  dist-eq-∧ = ∧-dist1 , ∧-dist2

  dist-eq-∨ : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∧ γ) ∼ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  dist-eq-∨ = ∨-dist1 , ∨-dist2


  ---------------------------------------------------------
  -- Lindenbaum-Tarski algebra is defined as the quotioent
  -- algebra obtained by factoring the algebra of formulas
  -- by the defined equivalence relation.
  ---------------------------------------------------------
  LindenbaumTarski : Type
  LindenbaumTarski = Formula / _∼_


  --------------------------------------------------
  -- The equivalence relation ∼ respects operations
  --------------------------------------------------

  ∼-respects-∧ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∧ b) ∼ (a' ∧ b')
  ∼-respects-∧ a a' b b' x y = ∧-I (⊢trans (∧-E₁ (axiom Z)) (proj₁ x))
                                   (⊢trans (∧-E₂ (axiom Z)) (proj₁ y)) ,
                               ∧-I (⊢trans (∧-E₁ (axiom Z)) (proj₂ x))
                                   (⊢trans (∧-E₂ (axiom Z)) (proj₂ y))
--  ∼-respects-∧ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∧ b) ∼ (a' ∧ b')
--  ∼-respects-∧ a a' b b' x y = (λ z → ∧-I (proj₁ x (∧-E₁ z)) (proj₁ y (∧-E₂ z))) ,
--                               (λ z → ∧-I (proj₂ x (∧-E₁ z)) (proj₂ y (∧-E₂ z)))

  ∼-respects-∨ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∨ b) ∼ (a' ∨ b')
  ∼-respects-∨ a a' b b' x y = ∨-E (axiom Z)
                                   (exchange (weakening (∨-I₂ (proj₁ x))))
                                   (exchange (weakening (∨-I₁ (proj₁ y)))) ,
                               ∨-E (axiom Z)
                                   (exchange (weakening (∨-I₂ (proj₂ x))))
                                   (exchange (weakening (∨-I₁ (proj₂ y))))
--  ∼-respects-∨ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∨ b) ∼ (a' ∨ b')
--  ∼-respects-∨ a a' b b' A B = (λ x → ∨-E x (λ x → ∨-I₂ (proj₁ A x)) λ x → ∨-I₁ (proj₁ B x)) , λ x → ∨-E x (λ x → ∨-I₂ (proj₂ A x)) λ x → ∨-I₁ (proj₂ B x)

  ∼-respects-¬ : ∀ (a a' : Formula) → a ∼ a' → (¬ a) ∼ (¬ a')
  ∼-respects-¬ a a' x = ¬-I (¬-E (exchange (weakening (proj₂ x))) (weakening (axiom Z))) ,
                        ¬-I (¬-E (exchange (weakening (proj₁ x))) (weakening (axiom Z)))
--  ∼-respects-¬ : ∀ (a a' : Formula) → a ∼ a' → (¬ a) ∼ (¬ a')
--  ∼-respects-¬ a a' A = (λ x → ¬-I (λ y → ¬-E (proj₂ A y) x)), (λ x → ¬-I (λ y → ¬-E (proj₁ A y) x))


  -------------------------------------------------------------------
  -- Definition: Binary operations and propositional constants in LT
  -------------------------------------------------------------------
  
  _⋀_ : LindenbaumTarski → LindenbaumTarski → LindenbaumTarski
  A ⋀ B = setQuotBinOp ∼-refl ∼-refl _∧_ ∼-respects-∧ A B

  _⋁_ : LindenbaumTarski  → LindenbaumTarski → LindenbaumTarski
  A ⋁ B = setQuotBinOp ∼-refl ∼-refl _∨_ ∼-respects-∨ A B

  ¬/_ : LindenbaumTarski → LindenbaumTarski
  ¬/ A = setQuotUnaryOp ¬_ ∼-respects-¬ A
  
  ⊤/ : LindenbaumTarski
  ⊤/ = [ ⊤ ]
  
  ⊥/ : LindenbaumTarski
  ⊥/ = [ ⊥ ]

 
  -- Commutativity on ⋀  
  ⋀-comm : ∀ (A B : LindenbaumTarski) → A ⋀ B ≡ B ⋀ A
  ⋀-comm = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ comm-eq-∧

-- elimProp2 (λ _ _ → squash/ _ _) λ ϕ ψ → eq/ _ _ (∼-sym (∧-comm , ∧-comm))

  -- Commutativity on ⋁
  ⋁-comm : ∀ (A B : LindenbaumTarski) → A ⋁ B ≡ B ⋁ A
  ⋁-comm = elimProp2 (λ _ _ → squash/ _ _) λ ϕ ψ → eq/ _ _ comm-eq-∨

  -- Associativity on ⋀
  ⋀-assoc : ∀ (A B C : LindenbaumTarski) → A ⋀ (B ⋀ C) ≡ (A ⋀ B) ⋀ C
  ⋀-assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ass-eq-∧

  --Associativity on ⋁
  ⋁-assoc : ∀ (A B C : LindenbaumTarski) → A ⋁ (B ⋁ C) ≡ (A ⋁ B) ⋁ C
  ⋁-assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ass-eq-∨

  -- Distributivity over ⋀
  ⋀-dist : ∀ (A B C : LindenbaumTarski) → A ⋀ (B ⋁ C) ≡ (A ⋀ B) ⋁ (A ⋀ C)
  ⋀-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ dist-eq-∧

  --Distributivity over ⋁
  ⋁-dist : ∀ (A B C : LindenbaumTarski) → A ⋁ (B ⋀ C) ≡ (A ⋁ B) ⋀ (A ⋁ C)
  ⋁-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ dist-eq-∨


  -- Definition: Superweakening
  superweakening : ∀ (Γ : ctxt) → Γ ⊢ ⊤
  superweakening ∅ = ⊤-I
  superweakening (Δ ∶ x) = weakening (superweakening Δ)


  -- Absorbtion law ⋁
  ⋁-abs : ∀ (A B : LindenbaumTarski) → (A ⋀ B) ⋁ B ≡ B
  ⋁-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∨-E (axiom Z) (∧-E₂ (axiom Z)) (axiom Z) , ∨-I₁ (axiom Z))
--  ⋁-abs : ∀ (A B : LindenbaumTarski) → (A ⋀ B) ⋁ B ≡ B
--  ⋁-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ((λ x → ∨-E x ∧-E₂ λ a → a) , ∨-I₁) 

  -- Absorbtion law ⋀
  ⋀-abs : ∀ (A B : LindenbaumTarski) → A ⋀ (A ⋁ B) ≡ A
  ⋀-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∧-E₁ (axiom Z) , ∧-I (axiom Z) (∨-I₂ (axiom Z)))
--  ⋀-abs : ∀ (A B : LindenbaumTarski) → A ⋀ (A ⋁ B) ≡ A
--  ⋀-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∧-E₁ , λ x → ∧-I x (∨-I₂ x))

  -- Identity law ⋁
  ⋁-id : ∀ (A : LindenbaumTarski) → A ⋁ ⊥/ ≡ A
  ⋁-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∨-E (axiom Z) (axiom Z) (⊥-E (axiom Z)) , ∨-I₂ (axiom Z))
--  ⋁-id : ∀ (A : LindenbaumTarski) → A ⋁ ⊥/ ≡ A
--  ⋁-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ((λ x → ∨-E x (λ y → y) ⊥-E) , ∨-I₂)

  -- Identity law ⋀
  ⋀-id : ∀ (A : LindenbaumTarski) → A ⋀ ⊤/ ≡ A
  ⋀-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∧-E₁ (axiom Z) , ∧-I (axiom Z) (superweakening _))
--  ⋀-id : ∀ (A : LindenbaumTarski) → A ⋀ ⊤/ ≡ A
--  ⋀-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∧-E₁ , λ x → ∧-I x (superweakening _))


  ------------------------------------------------------------
  -- If ϕ is provable in Γ then [ϕ] should be the same as ⊤/.
  -- We can view this as a form of soundness.
  ------------------------------------------------------------
  sound : ∀ {ϕ : Formula} → Γ ⊢ ϕ → [ ϕ ] ≡ ⊤/
  sound x = eq/ _ _ (superweakening _ , weakening x)
--  sound : ∀ {ϕ : Formula} → Γ ⊢ ϕ → [ ϕ ] ≡ ⊤/
--  sound x = eq/ _ _ ((λ _ → superweakening _) , λ _ → x )


  -------------------------------------------------------------
  -- By proving the Lindenbaum-Tarski algebra can be viewed as
  -- a distributive lattice, we prove that it is also boolean.
  -------------------------------------------------------------
  isSet-LT : ∀ (A B : LindenbaumTarski) → isProp(A ≡ B)
  isSet-LT A B = squash/ _ _

  --  LT-isDistLattice : IsDistLattice ⊥/ ⊤/ _⋁_ _⋀_
  --  LT-isDistLattice = makeIsDistLattice∧lOver∨l isSet-LT ⋁-assoc ⋁-id ⋁-comm ⋀-assoc ⋀-id ⋀-comm ⋀-abs ⋀-dist

  LindenbaumTarski-DistLattice : DistLattice _
  LindenbaumTarski-DistLattice = makeDistLattice∧lOver∨l ⊥/ ⊤/ _⋁_ _⋀_ isSet-LT ⋁-assoc ⋁-id ⋁-comm ⋀-assoc ⋀-id ⋀-comm ⋀-abs ⋀-dist


  {-
  open DistLattice         -- DistLattice (not in scope) -> DistLatticeStr? IsDistLattice?

  LindenbaumTarski-Boolean : (x y : fst LindenbaumTarski-DistLattice) -> x ∨l y ≡ 1l
  LindenbaumTarski-Boolean x y = {!!}
  -}


  -- Complemented
  ⋀-inv : ∀ (A : LindenbaumTarski) → A ⋀ ¬/ A ≡ ⊥/
  ⋀-inv = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (¬-E (∧-E₁ (axiom Z)) (∧-E₂ (axiom Z)) , ⊥-E (axiom Z))
--  ⋀-inv : ∀ (A : LindenbaumTarski) → A ⋀ ¬/ A ≡ ⊥/
--  ⋀-inv = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ((λ x → ¬-E (∧-E₁ x) (∧-E₂ x)) , λ x → ⊥-E x)
  
  ⋁-inv : ∀ (A : LindenbaumTarski) → A ⋁ ¬/ A ≡ ⊤/
  ⋁-inv = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (superweakening _ , LEM)
--  ⋁-inv : ∀ (A : LindenbaumTarski) → A ⋁ ¬/ A ≡ ⊤/
--  ⋁-inv = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ((λ x → superweakening _) , λ x → LEM)


  
