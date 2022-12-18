open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)


data Formula : Set where
  _∧_    : Formula → Formula → Formula
  _∨_    : Formula → Formula → Formula
  ¬_     : Formula → Formula
  const  : ℕ      → Formula
  ⊥      : Formula
  ⊤      : Formula


-- infixr eller infixl ? Varför?
infixl 30 _∧_ _∨_
infixl 25  ¬_


data _⊢_ : List Formula →  Formula → Set where

  ∧-intro : (Γ : List Formula) (ϕ ψ : Formula)
    → Γ ⊢ ϕ
    → Γ ⊢ ψ
       ---------
    → Γ ⊢ ϕ ∧ ψ
    
  ∧-elimˡ : (Γ : List Formula) (ϕ ψ : Formula)
    → Γ ⊢ ϕ ∧ ψ
      ----------
    → Γ ⊢ ϕ
    
  ∧-elimʳ : (Γ : List Formula) (ϕ ψ : Formula)
    → Γ ⊢ ϕ ∧ ψ
       ---------
    → Γ ⊢ ψ
  
  ∨-introʳ  : (Γ : List Formula) (ϕ ψ : Formula)
    → Γ ⊢ ψ
       ---------
    → Γ ⊢ ϕ ∨ ψ
    
  ∨-introˡ  : (Γ : List Formula) (ϕ ψ : Formula)
    → Γ ⊢ ϕ
       ---------
    → Γ ⊢ ϕ ∨ ψ

  ∨-elim : (Γ : List Formula) (ϕ ψ γ : Formula)
    → Γ ⊢ ϕ ∨ ψ
    → (ϕ ∷ Γ) ⊢ γ
    → (ψ ∷ Γ) ⊢ γ
       -----------
    → Γ ⊢ γ

  p∈Γ : (Γ : List Formula) (ϕ : Formula)
    → ϕ ∈ Γ
       -----
    → Γ ⊢ ϕ

  -- Antaget att Γ ⊬ ⊥ ?
  ¬intro : (Γ : List Formula) (ϕ : Formula)
    → (ϕ ∷ Γ) ⊢ ⊥
       ------------
    → Γ ⊢ ¬ ϕ
    
  ¬elim : (Γ : List Formula) (ϕ : Formula)
    → (¬ ϕ ∷ Γ) ⊢ ⊥
       --------------  Ok att ta för givet ¬¬ϕ ⊢ ϕ ? 
    → Γ ⊢ ϕ
    
