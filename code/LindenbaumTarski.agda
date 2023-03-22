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


data _∈_ : Formula → ctxt → Type where
  Z  : ∀ {Γ ϕ}   → ϕ ∈ (Γ ∶ ϕ)
  S_ : ∀ {Γ ϕ ψ} → ϕ ∈ Γ → ϕ ∈ (Γ ∶ ψ)


data _⊢_ : ctxt → Formula → Type where

  ∧-intro : {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ϕ → Γ ⊢ ψ → Γ ⊢ ϕ ∧ ψ
      
  ∧-elimˡ : {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ϕ ∧ ψ → Γ ⊢ ϕ
    
  ∧-elimʳ : {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ϕ ∧ ψ → Γ ⊢ ψ
  
  ∨-introˡ : {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ψ → Γ ⊢ ϕ ∨ ψ
    
  ∨-introʳ : {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ϕ → Γ ⊢ ϕ ∨ ψ

  ∨-elim : {Γ : ctxt} (ϕ ψ γ : Formula) → Γ ⊢ ϕ ∨ ψ → (Γ ∶ ϕ) ⊢ γ → (Γ ∶ ψ) ⊢ γ → Γ ⊢ γ

  ¬-intro : {Γ : ctxt} {ϕ : Formula} → (Γ ∶ ϕ) ⊢ ⊥ → Γ ⊢ ¬ ϕ

  ⊥-intro : {Γ : ctxt} {ϕ : Formula} → Γ ⊢ ϕ ∧ ¬ ϕ → Γ ⊢ ⊥

  ⊥-elim : {Γ : ctxt} {ϕ : Formula} → (Γ ∶ ⊥) ⊢ ϕ

  ⊤-intro : ∅ ⊢ ⊤

  axiom : {Γ : ctxt} {ϕ : Formula} → ϕ ∈ Γ → Γ ⊢ ϕ

  LEM : {Γ : ctxt} {ϕ : Formula} → Γ ⊢ ϕ ∨ ¬ ϕ

  weakening : {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ψ → (Γ ∶ ϕ) ⊢ ψ

  exchange : {Γ : ctxt} {ϕ ψ γ : Formula} → ((Γ ∶ ϕ) ∶ ψ) ⊢ γ → ((Γ ∶ ψ) ∶ ϕ) ⊢ γ

--  contraction : {Γ : ctxt} {ϕ ψ : Formula} → ((Γ ∶ ϕ) ∶ ϕ) ⊢ ψ → (Γ ∶ ϕ) ⊢ ψ
  

module _ {Γ : ctxt} where

  infixl 25 ¬/_

  -- Commutativity on ∧ and ∨

  ∧-comm : ∀ {ϕ ψ : Formula} → (Γ ∶ ϕ ∧ ψ) ⊢ ψ ∧ ϕ
  ∧-comm = ∧-intro (∧-elimʳ (axiom Z)) (∧-elimˡ (axiom Z))

  ∨-comm : {ϕ ψ : Formula} → (Γ ∶ ϕ ∨ ψ) ⊢ ψ ∨ ϕ
  ∨-comm = ∨-elim _ _ _ (axiom Z) (∨-introˡ (axiom Z)) (∨-introʳ (axiom Z))


  -- Associativity on ∧ and ∨

  ∧-assoc1 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ (ϕ ∧ ψ) ∧ γ) ⊢ ϕ ∧ (ψ ∧ γ)
  ∧-assoc1 = ∧-intro (∧-elimˡ (∧-elimˡ (axiom Z)))
                     (∧-intro (∧-elimʳ (∧-elimˡ (axiom Z)))
                              (∧-elimʳ (axiom Z)))

  ∧-assoc2 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ ϕ ∧ (ψ ∧ γ)) ⊢ (ϕ ∧ ψ) ∧ γ
  ∧-assoc2 = ∧-intro (∧-intro (∧-elimˡ (axiom Z))
                              (∧-elimˡ (∧-elimʳ (axiom Z))))
                     (∧-elimʳ (∧-elimʳ (axiom Z)))

  ∨-assoc1 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ (ϕ ∨ ψ) ∨ γ) ⊢ ϕ ∨ (ψ ∨ γ)
  ∨-assoc1 = ∨-elim _ _ _ (axiom Z)
                          (∨-elim _ _ _
                                  (axiom Z)
                                  (∨-introʳ (axiom Z))
                                  (∨-introˡ (∨-introʳ (axiom Z))))
                          (∨-introˡ  (∨-introˡ (axiom Z)))

  ∨-assoc2 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ ϕ ∨ (ψ ∨ γ)) ⊢ (ϕ ∨ ψ) ∨ γ
  ∨-assoc2 = ∨-elim _ _ _ (axiom Z)
                          (∨-introʳ (∨-introʳ (axiom Z)))
                          (∨-elim _ _ _
                                  (axiom Z)
                                  (∨-introʳ (∨-introˡ (axiom Z)))
                                  (∨-introˡ (axiom Z)))


  -- Distributivity over ∧ and ∨

  ∧-dist1 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ ϕ ∧ (ψ ∨ γ)) ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  ∧-dist1 = ∨-elim _ _ _ (∧-elimʳ (axiom Z))
                         (∨-introʳ (∧-intro (exchange (∧-elimˡ (axiom Z))) (axiom Z)))
                         (∨-introˡ (∧-intro (exchange (∧-elimˡ (axiom Z))) (axiom Z)))

  ∧-dist2 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)) ⊢ ϕ ∧ (ψ ∨ γ)
  ∧-dist2 = ∧-intro (∨-elim _ _ _ (axiom Z)
                                  (∧-elimˡ (axiom Z))
                                  (∧-elimˡ (axiom Z)))
                    (∨-elim _ _ _ (axiom Z)
                                  (∨-introʳ (∧-elimʳ (axiom Z)))
                                  (∨-introˡ (∧-elimʳ (axiom Z))))
  
  ∨-dist1 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ ϕ ∨ (ψ ∧ γ)) ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  ∨-dist1 = ∨-elim _ _ _ (axiom Z)
                         (∧-intro (∨-introʳ (axiom Z)) (∨-introʳ (axiom Z)))
                         (∧-intro (∨-introˡ (∧-elimˡ (axiom Z))) (∨-introˡ (∧-elimʳ (axiom Z))))
  
  ∨-dist2 : ∀ {ϕ ψ γ : Formula} → (Γ ∶ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)) ⊢ ϕ ∨ (ψ ∧ γ)
  ∨-dist2 {ϕ} {ψ} {γ} = ∨-elim _ _ _ (∧-elimˡ (axiom Z))
                                     (∨-elim _ ψ _
                                             (∨-introʳ (axiom Z))
                                             (∨-introʳ (axiom Z))
                                             (exchange (∨-introʳ (axiom Z))))
                                     (∨-elim _ γ _
                                             (exchange (∧-elimʳ (axiom Z)))
                                             (∨-introʳ (axiom Z))
                                             (∨-introˡ (∧-intro (exchange (axiom Z)) (axiom Z))))


  -- Equivalence relation
  
  _∼_ : Formula → Formula → Type
  ϕ ∼ ψ = (Γ ∶ ϕ) ⊢ ψ × (Γ ∶ ψ) ⊢ ϕ

  ∼-refl : ∀ (ϕ : Formula) → ϕ ∼ ϕ
  ∼-refl _ = axiom Z , (axiom Z)
  
  ∼-sym : ∀ {ϕ ψ : Formula} → ϕ ∼ ψ → ψ ∼ ϕ
  ∼-sym (A , B) = B , A
  
  ⊢trans : ∀ {ϕ ψ γ : Formula} → (Γ ∶ ϕ) ⊢ γ → (Γ ∶ γ) ⊢ ψ → (Γ ∶ ϕ) ⊢ ψ
  ⊢trans A B = ∨-elim _ _ _ (∨-introʳ A) (exchange (weakening B)) (axiom Z)
  
  ∼-trans : ∀ {ϕ ψ γ : Formula} → ϕ ∼ γ → γ ∼ ψ → ϕ ∼ ψ
  ∼-trans x y = ⊢trans (proj₁ x) (proj₁ y) , ⊢trans (proj₂ y) (proj₂ x)
  
  
  {- Lindenbaum-Tarski algebra -}
  
  LindenbaumTarski : Type
  LindenbaumTarski = Formula / _∼_
  
  
  -- Binary operations and propositional constants
  
  ∼-respects-∧ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∧ b) ∼ (a' ∧ b')
  ∼-respects-∧ a a' b b' x y = ∧-intro (⊢trans (∧-elimˡ (axiom Z)) (proj₁ x))
                                       (⊢trans (∧-elimʳ (axiom Z)) (proj₁ y)) ,
                               ∧-intro (⊢trans (∧-elimˡ (axiom Z)) (proj₂ x))
                                       (⊢trans (∧-elimʳ (axiom Z)) (proj₂ y))

  ∼-respects-∨ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∨ b) ∼ (a' ∨ b')
  ∼-respects-∨ a a' b b' x y = ∨-elim _ _ _ (axiom Z)
                                            (exchange (weakening (∨-introʳ (proj₁ x))))
                                            (exchange (weakening (∨-introˡ (proj₁ y)))) ,
                               ∨-elim _ _ _ (axiom Z)
                                            (exchange (weakening (∨-introʳ (proj₂ x))))
                                            (exchange (weakening (∨-introˡ (proj₂ y))))

  ∼-respects-¬ : ∀ (a a' : Formula) → a ∼ a' → (¬ a) ∼ (¬ a')
  ∼-respects-¬ a a' x = ¬-intro (⊥-intro (∧-intro (exchange (weakening (proj₂ x))) (weakening (axiom Z)))) ,
                        ¬-intro (⊥-intro (∧-intro (exchange (weakening (proj₁ x))) (weakening (axiom Z))))
  

  _⋀_ : LindenbaumTarski → LindenbaumTarski → LindenbaumTarski
  A ⋀ B = setQuotBinOp ∼-refl ∼-refl _∧_ ∼-respects-∧ A B

  _⋁_ : LindenbaumTarski → LindenbaumTarski → LindenbaumTarski
  A ⋁ B = setQuotBinOp ∼-refl ∼-refl _∨_ ∼-respects-∨ A B
  
  ¬/_ : LindenbaumTarski → LindenbaumTarski
  ¬/ A = setQuotUnaryOp ¬_ ∼-respects-¬ A
  
  ⊤/ : LindenbaumTarski
  ⊤/ = [ ⊤ ]
  
  ⊥/ : LindenbaumTarski
  ⊥/ = [ ⊥ ]

  
  -- Commutativity
  
  ⋀-comm : ∀ (A B : LindenbaumTarski) → A ⋀ B ≡ B ⋀ A
  ⋀-comm = elimProp2 (λ _ _ → squash/ _ _) λ ϕ ψ → eq/ _ _ (∼-sym (∧-comm , ∧-comm))

  ⋁-comm : ∀ (A B : LindenbaumTarski) → A ⋁ B ≡ B ⋁ A
  ⋁-comm = elimProp2 (λ _ _ → squash/ _ _) λ ϕ ψ → eq/ _ _ (∼-sym (∨-comm , ∨-comm))


  -- Associativity

  ⋀-assoc : ∀ (A B C : LindenbaumTarski) → A ⋀ (B ⋀ C) ≡ (A ⋀ B) ⋀ C
  ⋀-assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∧-assoc2 , ∧-assoc1)

  ⋁-assoc : ∀ (A B C : LindenbaumTarski) → A ⋁ (B ⋁ C) ≡ (A ⋁ B) ⋁ C
  ⋁-assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∨-assoc2 , ∨-assoc1)


  -- Distributivity

  ⋀-dist : ∀ (A B C : LindenbaumTarski) → A ⋀ (B ⋁ C) ≡ (A ⋀ B) ⋁ (A ⋀ C)
  ⋀-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∧-dist1 , ∧-dist2)

  ⋁-dist : ∀ (A B C : LindenbaumTarski) → A ⋁ (B ⋀ C) ≡ (A ⋁ B) ⋀ (A ⋁ C)
  ⋁-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∨-dist1 , ∨-dist2)


  -- Inverse element

  superweakening : ∀ (Γ : ctxt) → Γ ⊢ ⊤
  superweakening ∅ = ⊤-intro
  superweakening (Δ ∶ x) = weakening (superweakening Δ)

  ⋀-comp : ∀ (A : LindenbaumTarski) → A ⋀ ¬/ A ≡ ⊥/
  ⋀-comp = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (⊥-intro (axiom Z) , ⊥-elim)
  
  ⋁-comp : ∀ (A : LindenbaumTarski) → A ⋁ ¬/ A ≡ ⊤/
  ⋁-comp = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (superweakening _ , LEM)


  -- Absorbtion

  ⋁-abs : ∀ (A B : LindenbaumTarski) → (A ⋀ B) ⋁ B ≡ B
  ⋁-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∨-elim _ _ _ (axiom Z) (∧-elimʳ (axiom Z)) (axiom Z) , ∨-introˡ (axiom Z))

  ⋀-abs : ∀ (A B : LindenbaumTarski) → A ⋀ (A ⋁ B) ≡ A
  ⋀-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∧-elimˡ (axiom Z) , ∧-intro (axiom Z) (∨-introʳ (axiom Z)))


  -- Identity

  ⋁-id : ∀ (A : LindenbaumTarski) → A ⋁ ⊥/ ≡ A
  ⋁-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∨-elim _ _ _ (axiom Z) (axiom Z) ⊥-elim , ∨-introʳ (axiom Z))

  ⋀-id : ∀ (A : LindenbaumTarski) → A ⋀ ⊤/ ≡ A
  ⋀-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∧-elimˡ (axiom Z) , ∧-intro (axiom Z) (superweakening _))


  -- Soundness

  sound : ∀ {ϕ : Formula} → Γ ⊢ ϕ → [ ϕ ] ≡ ⊤/
  sound x = eq/ _ _ (superweakening _ , weakening x)



  {- LT is distributive lattice ⇒ LT boolean -}

  isSet-LT : ∀ (A B : LindenbaumTarski) → isProp(A ≡ B)
  isSet-LT A B = squash/ _ _

  LT-isDistLattice : LindenbaumTarski → IsDistLattice ⊥/ ⊤/ _⋁_ _⋀_
  LT-isDistLattice _ = makeIsDistLattice∧lOver∨l (λ _ _ → squash/ _ _)  -- isSet-LT
                                                 ⋁-assoc
                                                 ⋁-id
                                                 ⋁-comm
                                                 ⋀-assoc
                                                 ⋀-id
                                                 ⋀-comm
                                                 ⋀-abs
                                                 ⋀-dist
