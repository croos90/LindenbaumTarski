open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; [])
--open import Data.List.Membership.Propositional using (_∈_)


data Formula : Set where
  _∧_    : Formula → Formula → Formula
  _∨_    : Formula → Formula → Formula
  ¬_     : Formula → Formula
  const  : ℕ      → Formula
  ⊥      : Formula
  ⊤      : Formula


infix 35  _∧_
infix 30 _∨_
infix 25  ¬_



--------------------------------------------------
data ctxt : Set where
  ∅ : ctxt
  _,_ : ctxt → Formula → ctxt

data _∈_ : Formula → ctxt → Set where
  Z : ∀ {Γ ϕ} → ϕ ∈ (Γ , ϕ)
  S : ∀ {Γ ϕ ψ} → ϕ ∈ Γ → ϕ ∈ (Γ , ψ)
--------------------------------------------------



data _⊢_ : ctxt → Formula → Set where

  ∧-intro : (Γ : ctxt) (ϕ ψ : Formula)
    → Γ ⊢ ϕ
    → Γ ⊢ ψ
       ---------
    → Γ ⊢ ϕ ∧ ψ
    
  ∧-elimˡ : (Γ : ctxt) (ϕ ψ : Formula)
    → Γ ⊢ ϕ ∧ ψ
      ----------
    → Γ ⊢ ϕ
    
  ∧-elimʳ : (Γ : ctxt) (ϕ ψ : Formula)
    → Γ ⊢ ϕ ∧ ψ
       ---------
    → Γ ⊢ ψ
  
  ∨-introʳ  : (Γ : ctxt) (ϕ ψ : Formula)
    → Γ ⊢ ψ
       ---------
    → Γ ⊢ ϕ ∨ ψ
    
  ∨-introˡ  : (Γ : ctxt) (ϕ ψ : Formula)
    → Γ ⊢ ϕ
       ---------
    → Γ ⊢ ϕ ∨ ψ

  ∨-elim : (Γ : ctxt) (ϕ ψ γ : Formula)
    → Γ ⊢ ϕ ∨ ψ
    → (Γ , ϕ) ⊢ γ
    → (Γ , ψ) ⊢ γ
       -----------
    → Γ ⊢ γ

  p∈Γ : (Γ : ctxt) (ϕ : Formula)
    → ϕ ∈ Γ
       -----
    → Γ ⊢ ϕ

  ¬intro : (Γ : ctxt) (ϕ : Formula)
    → (Γ , ϕ) ⊢ ⊥
       ------------
    → Γ ⊢ ¬ ϕ
    
  ¬elim : (Γ : ctxt) (ϕ : Formula)
    → (Γ , ¬ ϕ) ⊢ ⊥
       -------------- 
    → Γ ⊢ ϕ

  ⊥-elim : (Γ : ctxt) (ϕ : Formula) → (Γ , ⊥) ⊢ ϕ

  ⊤-intro : ∅ ⊢ ⊤


-------------------------------------------------

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

-- Lägg till A × B → A etc. ?

data _∼_ : Formula → Formula → Set where
  ϕ∼ψ : (Γ : ctxt) (ϕ ψ : Formula) → ((Γ , ϕ) ⊢ ψ) × ((Γ , ψ) ⊢ ϕ) → ϕ ∼ ψ


∼-refl : ∀ {ϕ : Formula} {Γ : ctxt} → ϕ ∼ ϕ
∼-refl {ϕ} {Γ} = ϕ∼ψ Γ ϕ ϕ ⟨ p∈Γ (Γ , ϕ) ϕ Z , p∈Γ (Γ , ϕ) ϕ Z ⟩

∼-sym : ∀ {ϕ ψ : Formula} {Γ : ctxt} → ϕ ∼ ψ → ψ ∼ ϕ
∼-sym = {!!}

∼-trans : ∀ {ϕ ψ γ : Formula} {Γ : ctxt} → ϕ ∼ γ → γ ∼ ψ → ϕ ∼ ψ
∼-trans = {!!}
