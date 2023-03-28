{-# OPTIONS --cubical #-}
module LindenbaumTarski where


open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)

open import Cubical.Relation.Binary.Base

open import Cubical.Data.Nat.Base
open import Cubical.Data.Prod.Base

open import Cubical.Algebra.DistLattice.Base


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
infix  10  _∶_
 

data ctxt : Type where
  ∅    : ctxt
  _∶_  : ctxt → Formula → ctxt

{-
data _∈_ : Formula → ctxt → Type where
  Z  : ∀ {Γ ϕ}   → ϕ ∈ (Γ ∶ ϕ)
  S_ : ∀ {Γ ϕ ψ} → ϕ ∈ Γ → ϕ ∈ (Γ ∶ ψ)
-}


{-# NO_POSITIVITY_CHECK #-}

data _⊢_ : ctxt → Formula → Type where
  ∧-intro : {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ϕ → Γ ⊢ ψ → Γ ⊢ ϕ ∧ ψ
  ∧-elimˡ : {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ϕ ∧ ψ → Γ ⊢ ϕ
  ∧-elimʳ : {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ϕ ∧ ψ → Γ ⊢ ψ
  
  ∨-introˡ : {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ψ → Γ ⊢ ϕ ∨ ψ
  ∨-introʳ : {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ϕ → Γ ⊢ ϕ ∨ ψ
--  ∨-elim : {Γ : ctxt} (ϕ ψ γ : Formula) → Γ ⊢ ϕ ∨ ψ → (Γ ∶ ϕ) ⊢ γ → (Γ ∶ ψ) ⊢ γ → Γ ⊢ γ
  ∨-elim : {Γ : ctxt} {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∨ ψ → (Γ ⊢ ϕ → Γ ⊢ γ) → (Γ ⊢ ψ → Γ ⊢ γ) → Γ ⊢ γ

--  ¬-intro : {Γ : ctxt} {ϕ : Formula} → (Γ ∶ ϕ) ⊢ ⊥ → Γ ⊢ ¬ ϕ
  ¬-intro : {Γ : ctxt} {ϕ : Formula} → (Γ ⊢ ϕ → Γ ⊢ ⊥) → Γ ⊢ ¬ ϕ
  ¬-elim : {Γ : ctxt} {ϕ : Formula} → Γ ⊢ ⊥ → Γ ⊢ ϕ
  
  ⊥-intro : {Γ : ctxt} {ϕ : Formula} → Γ ⊢ ϕ → Γ ⊢ ¬ ϕ → Γ ⊢ ⊥
  
  ⊤-intro : ∅ ⊢ ⊤
  
--  axiom : {Γ : ctxt} {ϕ : Formula} → ϕ ∈ Γ → Γ ⊢ ϕ
  LEM : {Γ : ctxt} {ϕ : Formula} → Γ ⊢ ϕ ∨ ¬ ϕ
  
  weakening : {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ψ → (Γ ∶ ϕ) ⊢ ψ
--  exchange : {Γ : ctxt} {ϕ ψ γ : Formula} → ((Γ ∶ ϕ) ∶ ψ) ⊢ γ → ((Γ ∶ ψ) ∶ ϕ) ⊢ γ
--  contraction : {Γ : ctxt} {ϕ ψ : Formula} → ((Γ ∶ ϕ) ∶ ϕ) ⊢ ψ → (Γ ∶ ϕ) ⊢ ψ


module _ {Γ : ctxt} where

  infixl 25 ¬/_

  -- Commutativity on ∧ and ∨

--  ∧-comm : ∀ {ϕ ψ : Formula} → (Γ ∶ ϕ ∧ ψ) ⊢ ψ ∧ ϕ
--  ∧-comm = ∧-intro (∧-elimʳ (axiom Z)) (∧-elimˡ (axiom Z))
  ∧-comm : ∀ {ϕ ψ : Formula} → Γ ⊢ ϕ ∧ ψ → Γ ⊢ ψ ∧ ϕ
  ∧-comm x = ∧-intro (∧-elimʳ x) (∧-elimˡ x)

--  ∨-comm : {ϕ ψ : Formula} → (Γ ∶ ϕ ∨ ψ) ⊢ ψ ∨ ϕ
--  ∨-comm = ∨-elim _ _ _ (axiom Z) (∨-introˡ (axiom Z)) (∨-introʳ (axiom Z))
  ∨-comm : {ϕ ψ : Formula} → Γ ⊢ ϕ ∨ ψ → Γ ⊢ ψ ∨ ϕ
  ∨-comm x = ∨-elim x ∨-introˡ ∨-introʳ


  -- Associativity on ∧ and ∨

--  ∧-assoc2 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ (ϕ ∧ ψ) ∧ γ) ⊢ ϕ ∧ (ψ ∧ γ)
--  ∧-assoc2 = ∧-intro (∧-elimˡ (∧-elimˡ (axiom Z)))
--                     (∧-intro (∧-elimʳ (∧-elimˡ (axiom Z)))
--                              (∧-elimʳ (axiom Z)))
  ∧-assoc2 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ∧ ψ) ∧ γ → Γ ⊢ ϕ ∧ (ψ ∧ γ)
  ∧-assoc2 x = ∧-intro (∧-elimˡ (∧-elimˡ x))
                       (∧-intro (∧-elimʳ (∧-elimˡ x)) (∧-elimʳ x))

--  ∧-assoc1 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ ϕ ∧ (ψ ∧ γ)) ⊢ (ϕ ∧ ψ) ∧ γ
--  ∧-assoc1 = ∧-intro (∧-intro (∧-elimˡ (axiom Z))
--                              (∧-elimˡ (∧-elimʳ (axiom Z))))
--                     (∧-elimʳ (∧-elimʳ (axiom Z)))
  ∧-assoc1 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∧ (ψ ∧ γ) → Γ ⊢ (ϕ ∧ ψ) ∧ γ
  ∧-assoc1 x = ∧-intro (∧-intro (∧-elimˡ x) (∧-elimˡ (∧-elimʳ x)))
                       (∧-elimʳ (∧-elimʳ x))

--  ∨-assoc2 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ (ϕ ∨ ψ) ∨ γ) ⊢ ϕ ∨ (ψ ∨ γ)
--  ∨-assoc2 = ∨-elim _ _ _ (axiom Z)
--                          (∨-elim _ _ _
--                                  (axiom Z)
--                                  (∨-introʳ (axiom Z))
--                                  (∨-introˡ (∨-introʳ (axiom Z))))
--                          (∨-introˡ  (∨-introˡ (axiom Z)))
  ∨-assoc2 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ∨ ψ) ∨ γ → Γ ⊢ ϕ ∨ (ψ ∨ γ)
  ∨-assoc2 x = ∨-elim x (λ y → ∨-elim y ∨-introʳ λ z → ∨-introˡ (∨-introʳ z))
                      λ y → ∨-introˡ (∨-introˡ y)

--  ∨-assoc1 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ ϕ ∨ (ψ ∨ γ)) ⊢ (ϕ ∨ ψ) ∨ γ
--  ∨-assoc1 = ∨-elim _ _ _ (axiom Z)
--                          (∨-introʳ (∨-introʳ (axiom Z)))
--                          (∨-elim _ _ _
--                                  (axiom Z)
--                                  (∨-introʳ (∨-introˡ (axiom Z)))
--                                  (∨-introˡ (axiom Z)))
  ∨-assoc1 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∨ (ψ ∨ γ) → Γ ⊢ (ϕ ∨ ψ) ∨ γ
  ∨-assoc1 x = ∨-elim x (λ y → ∨-introʳ (∨-introʳ y)) λ y → ∨-elim y (λ z → ∨-introʳ (∨-introˡ z)) ∨-introˡ


  -- Distributivity over ∧ and ∨

--  ∧-dist1 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ ϕ ∧ (ψ ∨ γ)) ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
--  ∧-dist1 = ∨-elim _ _ _ (∧-elimʳ (axiom Z))
--                         (∨-introʳ (∧-intro (exchange (∧-elimˡ (axiom Z))) (axiom Z)))
--                         (∨-introˡ (∧-intro (exchange (∧-elimˡ (axiom Z))) (axiom Z)))
  ∧-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∧ (ψ ∨ γ) → Γ ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  ∧-dist1 x = ∨-elim (∧-elimʳ x) (λ y → ∨-introʳ (∧-intro (∧-elimˡ x) y))
                              λ y → ∨-introˡ (∧-intro (∧-elimˡ x) y)

--  ∧-dist2 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)) ⊢ ϕ ∧ (ψ ∨ γ)
--  ∧-dist2 = ∧-intro (∨-elim _ _ _ (axiom Z)
--                                  (∧-elimˡ (axiom Z))
--                                  (∧-elimˡ (axiom Z)))
--                    (∨-elim _ _ _ (axiom Z)
--                                  (∨-introʳ (∧-elimʳ (axiom Z)))
--                                  (∨-introˡ (∧-elimʳ (axiom Z))))
  ∧-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ) → Γ ⊢ ϕ ∧ (ψ ∨ γ)
  ∧-dist2 x = ∧-intro (∨-elim x ∧-elimˡ ∧-elimˡ)
                      (∨-elim x (λ y → ∨-introʳ (∧-elimʳ y))
                              λ y → ∨-introˡ (∧-elimʳ y))

--  ∨-dist1 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ ϕ ∨ (ψ ∧ γ)) ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
--  ∨-dist1 = ∨-elim _ _ _ (axiom Z)
--                         (∧-intro (∨-introʳ (axiom Z)) (∨-introʳ (axiom Z)))
--                         (∧-intro (∨-introˡ (∧-elimˡ (axiom Z))) (∨-introˡ (∧-elimʳ (axiom Z))))
  ∨-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∨ (ψ ∧ γ) → Γ ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  ∨-dist1 x = ∨-elim x (λ y → ∧-intro (∨-introʳ y) (∨-introʳ y))
                     λ y → ∧-intro (∨-introˡ (∧-elimˡ y)) (∨-introˡ (∧-elimʳ y))
  
--  ∨-dist2 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)) ⊢ ϕ ∨ (ψ ∧ γ)
--  ∨-dist2 {ϕ} {ψ} {γ} = ∨-elim _ _ _ (∧-elimˡ (axiom Z))
--                                     (∨-elim _ ψ _
--                                             (∨-introʳ (axiom Z))
--                                             (∨-introʳ (axiom Z))
--                                             (weakening (∨-introʳ (axiom Z))) )
--                                     (∨-elim _ γ _
--                                             (exchange (∧-elimʳ (axiom Z)))
--                                             (∨-introʳ (axiom Z))
--                                             (∨-introˡ (∧-intro (weakening (axiom Z)) (axiom Z))))
  ∨-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ) → Γ ⊢ ϕ ∨ (ψ ∧ γ)
  ∨-dist2 x = ∨-elim (∧-elimˡ x) ∨-introʳ λ y → ∨-elim (∧-elimʳ x) ∨-introʳ λ z → ∨-introˡ (∧-intro y z)


  -- Equivalence relation
  
--  _∼_ : Formula → Formula → Type
--  ϕ ∼ ψ = (Γ ∶ ϕ) ⊢ ψ × (Γ ∶ ψ) ⊢ ϕ
  _∼_ : Formula → Formula → Type
  ϕ ∼ ψ = (Γ ⊢ ϕ → Γ ⊢ ψ) × (Γ ⊢ ψ → Γ ⊢ ϕ)

--  ∼-refl : ∀ (ϕ : Formula) → ϕ ∼ ϕ
--  ∼-refl _ = axiom Z , (axiom Z)
  ∼-refl : ∀ (ϕ : Formula) → ϕ ∼ ϕ
  ∼-refl _ = (λ x → x) , (λ x → x)
  
  ∼-sym : ∀ {ϕ ψ : Formula} → ϕ ∼ ψ → ψ ∼ ϕ
  ∼-sym (A , B) = B , A

--  ⊢trans : ∀ {ϕ ψ γ : Formula} → (Γ ∶ ϕ) ⊢ γ → (Γ ∶ γ) ⊢ ψ → (Γ ∶ ϕ) ⊢ ψ
--  ⊢trans A B = ∨-elim _ _ _ (∨-introʳ A) (exchange (weakening B)) (axiom Z)
  ⊢trans : ∀ {ϕ ψ γ : Formula} → (Γ ⊢ ϕ → Γ ⊢ ψ) → (Γ ⊢ ψ → Γ ⊢ γ) → (Γ ⊢ ϕ → Γ ⊢ γ)
  ⊢trans x y z = y (x z)
  
--  ∼-trans : ∀ {ϕ ψ γ : Formula} → ϕ ∼ γ → γ ∼ ψ → ϕ ∼ ψ
--  ∼-trans x y = ⊢trans (proj₁ x) (proj₁ y) , ⊢trans (proj₂ y) (proj₂ x)
  ∼-trans : ∀ {ϕ ψ γ : Formula} → ϕ ∼ γ → γ ∼ ψ → ϕ ∼ ψ
  ∼-trans x y = ⊢trans (proj₁ x) (proj₁ y) , ⊢trans (proj₂ y) (proj₂ x)
  


  {- Lindenbaum-Tarski algebra -}
  
  LindenbaumTarski : Type
  LindenbaumTarski = Formula / _∼_
  
  
  -- Binary operations and propositional constants

--  ∼-respects-∧ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∧ b) ∼ (a' ∧ b')
--  ∼-respects-∧ a a' b b' x y = ∧-intro (⊢trans (∧-elimˡ (axiom Z)) (proj₁ x))
--                                       (⊢trans (∧-elimʳ (axiom Z)) (proj₁ y)) ,
--                               ∧-intro (⊢trans (∧-elimˡ (axiom Z)) (proj₂ x))
--                                       (⊢trans (∧-elimʳ (axiom Z)) (proj₂ y))
  ∼-respects-∧ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∧ b) ∼ (a' ∧ b')
  ∼-respects-∧ a a' b b' x y = (λ z → ∧-intro (proj₁ x (∧-elimˡ z)) (proj₁ y (∧-elimʳ z))) ,
                               (λ z → ∧-intro (proj₂ x (∧-elimˡ z)) (proj₂ y (∧-elimʳ z)))


--  ∼-respects-∨ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∨ b) ∼ (a' ∨ b')
--  ∼-respects-∨ a a' b b' x y = ∨-elim _ _ _ (axiom Z)
--                                            (exchange (weakening (∨-introʳ (proj₁ x))))
--                                            (exchange (weakening (∨-introˡ (proj₁ y)))) ,
--                               ∨-elim _ _ _ (axiom Z)
--                                            (exchange (weakening (∨-introʳ (proj₂ x))))
--                                            (exchange (weakening (∨-introˡ (proj₂ y))))
  ∼-respects-∨ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∨ b) ∼ (a' ∨ b')
  ∼-respects-∨ a a' b b' A B = (λ x → ∨-elim x (λ x → ∨-introʳ (proj₁ A x)) λ x → ∨-introˡ (proj₁ B x)) ,
                                λ x → ∨-elim x (λ x → ∨-introʳ (proj₂ A x)) λ x → ∨-introˡ (proj₂ B x)


--  ∼-respects-¬ : ∀ (a a' : Formula) → a ∼ a' → (¬ a) ∼ (¬ a')
--  ∼-respects-¬ a a' x = ¬-intro (⊥-intro (exchange (weakening (proj₂ x))) (weakening (axiom Z))) ,
--                        ¬-intro (⊥-intro (exchange (weakening (proj₁ x))) (weakening (axiom Z)))
  ∼-respects-¬ : ∀ (a a' : Formula) → a ∼ a' → (¬ a) ∼ (¬ a')
  ∼-respects-¬ a a' A = (λ x → ¬-intro (λ y → ⊥-intro (proj₂ A y) x)),
                        (λ x → ¬-intro (λ y → ⊥-intro (proj₁ A y) x))


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

  
  -- Commutativity
  
--  ⋀-comm : ∀ (A B : LindenbaumTarski) → A ⋀ B ≡ B ⋀ A
--  ⋀-comm = elimProp2 (λ _ _ → squash/ _ _) λ ϕ ψ → eq/ _ _ (∼-sym (∧-comm , ∧-comm))
  ⋀-comm : ∀ (A B : LindenbaumTarski) → A ⋀ B ≡ B ⋀ A
  ⋀-comm = elimProp2 (λ _ _ → squash/ _ _) λ ϕ ψ → eq/ _ _ (∼-sym (∧-comm , ∧-comm))

--  ⋁-comm : ∀ (A B : LindenbaumTarski) → A ⋁ B ≡ B ⋁ A
--  ⋁-comm =  elimProp2 (λ _ _ → squash/ _ _) λ ϕ ψ → eq/ _ _ (∼-sym (∨-comm , ∨-comm))
  ⋁-comm : ∀ (A B : LindenbaumTarski) → A ⋁ B ≡ B ⋁ A
  ⋁-comm =  elimProp2 (λ _ _ → squash/ _ _) λ ϕ ψ → eq/ _ _ (∼-sym (∨-comm , ∨-comm))


  -- Associativity

--  ⋀-assoc : ∀ (A B C : LindenbaumTarski) → A ⋀ (B ⋀ C) ≡ (A ⋀ B) ⋀ C
--  ⋀-assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∧-assoc1 , ∧-assoc2)
  ⋀-assoc : ∀ (A B C : LindenbaumTarski) → A ⋀ (B ⋀ C) ≡ (A ⋀ B) ⋀ C
  ⋀-assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∧-assoc1 , ∧-assoc2)

--  ⋁-assoc : ∀ (A B C : LindenbaumTarski) → A ⋁ (B ⋁ C) ≡ (A ⋁ B) ⋁ C
--  ⋁-assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∨-assoc1 , ∨-assoc2)
  ⋁-assoc : ∀ (A B C : LindenbaumTarski) → A ⋁ (B ⋁ C) ≡ (A ⋁ B) ⋁ C
  ⋁-assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∨-assoc1 , ∨-assoc2)


  -- Distributivity

--  ⋀-dist : ∀ (A B C : LindenbaumTarski) → A ⋀ (B ⋁ C) ≡ (A ⋀ B) ⋁ (A ⋀ C)
--  ⋀-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∧-dist1 , ∧-dist2)
  ⋀-dist : ∀ (A B C : LindenbaumTarski) → A ⋀ (B ⋁ C) ≡ (A ⋀ B) ⋁ (A ⋀ C)
  ⋀-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∧-dist1 , ∧-dist2)

--  ⋁-dist : ∀ (A B C : LindenbaumTarski) → A ⋁ (B ⋀ C) ≡ (A ⋁ B) ⋀ (A ⋁ C)
--  ⋁-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∨-dist1 , ∨-dist2)
  ⋁-dist : ∀ (A B C : LindenbaumTarski) → A ⋁ (B ⋀ C) ≡ (A ⋁ B) ⋀ (A ⋁ C)
  ⋁-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∨-dist1 , ∨-dist2)


  -- Inverse element (Not needed anymore since DistLattice uses identity?)

  superweakening : ∀ (Γ : ctxt) → Γ ⊢ ⊤
  superweakening ∅ = ⊤-intro
  superweakening (Δ ∶ x) = weakening (superweakening Δ)

--  ⋀-inv : ∀ (A : LindenbaumTarski) → A ⋀ ¬/ A ≡ ⊥/
--  ⋀-inv = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (⊥-intro (∧-elimˡ (axiom Z)) (∧-elimʳ (axiom Z)) , ¬-elim (axiom Z))
  ⋀-inv : ∀ (A : LindenbaumTarski) → A ⋀ ¬/ A ≡ ⊥/
  ⋀-inv = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ((λ x → ⊥-intro (∧-elimˡ x) (∧-elimʳ x)) , λ x → ¬-elim x)
  
--  ⋁-inv : ∀ (A : LindenbaumTarski) → A ⋁ ¬/ A ≡ ⊤/
--  ⋁-inv = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (superweakening _ , LEM)
  ⋁-inv : ∀ (A : LindenbaumTarski) → A ⋁ ¬/ A ≡ ⊤/
  ⋁-inv = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ((λ x → superweakening _) , λ x → LEM)


-- Absorbtion

--  ⋁-abs : ∀ (A B : LindenbaumTarski) → (A ⋀ B) ⋁ B ≡ B
--  ⋁-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∨-elim _ _ _ (axiom Z) (∧-elimʳ (axiom Z)) (axiom Z) , ∨-introˡ (axiom Z))
  ⋁-abs : ∀ (A B : LindenbaumTarski) → (A ⋀ B) ⋁ B ≡ B
  ⋁-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ((λ x → ∨-elim x ∧-elimʳ λ a → a) , ∨-introˡ) 

--  ⋀-abs : ∀ (A B : LindenbaumTarski) → A ⋀ (A ⋁ B) ≡ A
--  ⋀-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∧-elimˡ (axiom Z) , ∧-intro (axiom Z) (∨-introʳ (axiom Z)))
  ⋀-abs : ∀ (A B : LindenbaumTarski) → A ⋀ (A ⋁ B) ≡ A
  ⋀-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∧-elimˡ , λ x → ∧-intro x (∨-introʳ x))


  -- Identity

--  ⋁-id : ∀ (A : LindenbaumTarski) → A ⋁ ⊥/ ≡ A
--  ⋁-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∨-elim _ _ _ (axiom Z) (axiom Z) (¬-elim (axiom Z)) , ∨-introʳ (axiom Z))
  ⋁-id : ∀ (A : LindenbaumTarski) → A ⋁ ⊥/ ≡ A
  ⋁-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ((λ x → ∨-elim x (λ y → y) ¬-elim) , ∨-introʳ)

--  ⋀-id : ∀ (A : LindenbaumTarski) → A ⋀ ⊤/ ≡ A
--  ⋀-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∧-elimˡ (axiom Z) , ∧-intro (axiom Z) (superweakening _))
  ⋀-id : ∀ (A : LindenbaumTarski) → A ⋀ ⊤/ ≡ A
  ⋀-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∧-elimˡ , λ x → ∧-intro x (superweakening _))


  -- Soundness

--  sound : ∀ {ϕ : Formula} → Γ ⊢ ϕ → [ ϕ ] ≡ ⊤/
--  sound x = eq/ _ _ (superweakening _ , weakening x)
  sound : ∀ {ϕ : Formula} → Γ ⊢ ϕ → [ ϕ ] ≡ ⊤/
  sound x = eq/ _ _ ((λ _ → superweakening _) , λ _ → x )



  {- LT is distributive lattice ⇒ LT boolean -}

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
