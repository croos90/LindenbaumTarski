-- {-# OPTIONS --cubical-compatible #-}
{-# OPTIONS --cubical #-}


module satslogik where

-- open import Data.Nat using (ℕ)
open import Cubical.HITs.SetQuotients.Base

data Formula : Set where
  _∧_    : Formula → Formula → Formula
  _∨_    : Formula → Formula → Formula
  ¬_     : Formula → Formula
--  const  : ℕ      → Formula
  ⊥      : Formula
  ⊤      : Formula


infix 35  _∧_
infix 30 _∨_
infix 25  ¬_
infix 15 _×_
infix 20 _⊢_
infix 10 _,_
 

data ctxt : Set where
  ∅ : ctxt
  _,_ : ctxt → Formula → ctxt

data _∈_ : Formula → ctxt → Set where
  Z : ∀ {Γ ϕ} → ϕ ∈ (Γ , ϕ)
  S_ : ∀ {Γ ϕ ψ} → ϕ ∈ Γ → ϕ ∈ (Γ , ψ)

data _⊢_ : ctxt → Formula → Set where

  ∧-intro : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ϕ → Γ ⊢ ψ → Γ ⊢ ϕ ∧ ψ
    
  ∧-elimˡ : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ϕ ∧ ψ → Γ ⊢ ϕ
    
  ∧-elimʳ : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ϕ ∧ ψ → Γ ⊢ ψ
  
  ∨-introˡ : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ψ → Γ ⊢ ϕ ∨ ψ
    
  ∨-introʳ : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ϕ → Γ ⊢ ϕ ∨ ψ

  ∨-elim : (Γ : ctxt) (ϕ ψ γ : Formula) → Γ ⊢ ϕ ∨ ψ → (Γ , ϕ) ⊢ γ → (Γ , ψ) ⊢ γ → Γ ⊢ γ

  ¬intro : (Γ : ctxt) (ϕ : Formula) → (Γ , ϕ) ⊢ ⊥ → Γ ⊢ ¬ ϕ
    
  ¬elim : (Γ : ctxt) (ϕ : Formula) → (Γ , ¬ ϕ) ⊢ ⊥ → Γ ⊢ ϕ

  ⊥-elim : (Γ : ctxt) (ϕ : Formula) → (Γ , ⊥) ⊢ ϕ

  ⊤-intro : ∅ ⊢ ⊤

  axiom : (Γ : ctxt) (ϕ : Formula) → ϕ ∈ Γ → Γ ⊢ ϕ

  weakening : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ψ → (Γ , ϕ) ⊢ ψ

  exchange : (Γ : ctxt) (ϕ ψ γ : Formula) → ((Γ , ϕ) , ψ) ⊢ γ → ((Γ , ψ) , ϕ) ⊢ γ

  contraction : (Γ : ctxt) (ϕ ψ : Formula) → ((Γ , ϕ) , ϕ) ⊢ ψ → (Γ , ϕ) ⊢ ψ


data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

×-fst : ∀ {A B : Set} → A × B → A
×-fst ⟨ A , B ⟩  = A

×-snd : ∀ {A B : Set} → A × B → B
×-snd ⟨ A , B ⟩ = B


module _ {Γ : ctxt} where

  -- Equivalence relation
  _∼_ : Formula → Formula → Set
  ϕ ∼ ψ = (Γ , ϕ) ⊢ ψ × (Γ , ψ) ⊢ ϕ

  ∼-refl : ∀ {ϕ : Formula} → ϕ ∼ ϕ
  ∼-refl {ϕ} = ⟨ axiom (_ , ϕ) ϕ Z , (axiom (_ , ϕ) ϕ Z) ⟩

  ∼-sym : ∀ {ϕ ψ : Formula} → ϕ ∼ ψ → ψ ∼ ϕ
  ∼-sym ⟨ A , B ⟩ = ⟨ B , A ⟩

  lemma : ∀ {ϕ ψ γ : Formula} → (Γ , ϕ) ⊢ γ → (Γ , γ) ⊢ ψ → (Γ , ϕ) ⊢ ψ
  lemma {ϕ} {ψ} {γ} A B = ∨-elim (_ , ϕ) γ ψ ψ (∨-introʳ (_ , ϕ) γ ψ A) (exchange _ γ ϕ ψ (weakening (_ , γ) ϕ ψ B)) (axiom ((_ , ϕ) , ψ) ψ Z)

  ∼-trans : ∀ {ϕ ψ γ : Formula} → ϕ ∼ γ → γ ∼ ψ → ϕ ∼ ψ
  ∼-trans x y = ⟨ lemma (×-fst x) (×-fst y) , lemma (×-snd y) (×-snd x) ⟩



  -- Lindenbaum-Tarski algebra

  LT : Set
  LT = Formula / _∼_


  -- Define ⋀ ⋁ ¬ ⊤ ⊥

  _⋀_ : LT → LT → LT      -- Paaaattern matching
  [ a ] ⋀ [ b ] = [ a ∧ b ]


















{-
-- Equivalence
_⊢_∼_ : ctxt → Formula → Formula → Set
Γ ⊢ ϕ ∼ ψ = ((Γ , ϕ) ⊢ ψ) × ((Γ , ψ) ⊢ ϕ)

-- Reflexivity
∼-refl : ∀ {ϕ : Formula} {Γ : ctxt} → Γ ⊢ ϕ ∼ ϕ
∼-refl {ϕ} {Γ} = ⟨ axiom (Γ , ϕ) ϕ Z , (axiom (Γ , ϕ) ϕ Z) ⟩


-- Symmetry
∼-sym : ∀ {ϕ ψ : Formula} {Γ : ctxt} → Γ ⊢ ϕ ∼ ψ → Γ ⊢ ψ ∼ ϕ
∼-sym ⟨ A , B ⟩ = ⟨ B , A ⟩


-- Lemma (for transitivity)
-------------------------------------------------------------------
-- [ Γ , ϕ      ⊢ γ ∨ ψ ]:    (∨-introˡ (Γ , ϕ) γ ψ Γ,ϕ⊢γ)
-- [ Γ , ϕ , γ  ⊢ ψ     ]:    (exchange Γ γ ϕ ψ (weakening (Γ , γ) ϕ ψ Γ,γ⊢ψ))
-- [ Γ , ϕ , ψ  ⊢ ψ     ]:    (axiom ((Γ , ϕ) , ψ) ψ Z)
-- [ Γ , ϕ      ⊢ ψ     ]:    ∨-elim (∨-introˡ (Γ , ϕ) ψ Γ,ϕ⊢γ) (weakening (Γ , γ) ϕ ψ Γ,γ⊢ψ) (axiom (Γ , ϕ , ψ) ψ Z)
-------------------------------------------------------------------
-- Namn?
lemma : ∀ {ϕ ψ γ : Formula} {Γ : ctxt} → (Γ , ϕ) ⊢ γ → (Γ , γ) ⊢ ψ → (Γ , ϕ) ⊢ ψ
lemma {ϕ} {ψ} {γ} {Γ} A B = ∨-elim (Γ , ϕ) γ ψ ψ (∨-introʳ (Γ , ϕ) γ ψ A) (exchange Γ γ ϕ ψ (weakening (Γ , γ) ϕ ψ B)) (axiom ((Γ , ϕ) , ψ) ψ Z)


-- Transitivity
∼-trans : ∀ {ϕ ψ γ : Formula} {Γ : ctxt} → Γ ⊢ ϕ ∼ γ → Γ ⊢ γ ∼ ψ → Γ ⊢ ϕ ∼ ψ
∼-trans x y = ⟨ lemma (×-fst x) (×-fst y) , lemma (×-snd y) (×-snd x) ⟩

-}
