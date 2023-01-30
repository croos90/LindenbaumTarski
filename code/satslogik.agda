open import Data.Nat using (ℕ)

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

  p∈Γ : (Γ : ctxt) (ϕ : Formula) → ϕ ∈ Γ → Γ ⊢ ϕ

  ¬intro : (Γ : ctxt) (ϕ : Formula) → (Γ , ϕ) ⊢ ⊥ → Γ ⊢ ¬ ϕ
    
  ¬elim : (Γ : ctxt) (ϕ : Formula) → (Γ , ¬ ϕ) ⊢ ⊥ → Γ ⊢ ϕ

  ⊥-elim : (Γ : ctxt) (ϕ : Formula) → (Γ , ⊥) ⊢ ϕ

  ⊤-intro : ∅ ⊢ ⊤
------------------------------------------------------------------------------------
  ext : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ψ → (Γ , ϕ) ⊢ ψ

  rearrange : (Γ : ctxt) (ϕ ψ γ : Formula) → ((Γ , ϕ) , ψ) ⊢ γ → ((Γ , ψ) , ϕ) ⊢ γ
------------------------------------------------------------------------------------

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

×-projₗ : ∀ {A B : Set} → A × B → A
×-projₗ ⟨ A , B ⟩  = A

×-projᵣ : ∀ {A B : Set} → A × B → B
×-projᵣ ⟨ A , B ⟩ = B

_⊢_∼_ : ctxt → Formula → Formula → Set
Γ ⊢ ϕ ∼ ψ = ((Γ , ϕ) ⊢ ψ) × ((Γ , ψ) ⊢ ϕ)

∼-refl : ∀ {ϕ : Formula} {Γ : ctxt} → Γ ⊢ ϕ ∼ ϕ
∼-refl {ϕ} {Γ} = ⟨ p∈Γ (Γ , ϕ) ϕ Z , (p∈Γ (Γ , ϕ) ϕ Z) ⟩

∼-sym : ∀ {ϕ ψ : Formula} {Γ : ctxt} → Γ ⊢ ϕ ∼ ψ → Γ ⊢ ψ ∼ ϕ
∼-sym ⟨ A , B ⟩ = ⟨ ×-projᵣ ⟨ A , B ⟩ , ×-projₗ ⟨ A , B ⟩ ⟩


-------------------------------------------------------------------
-- Lemma
⊢-trans : ∀ {ϕ ψ γ : Formula} {Γ : ctxt} → (Γ , ϕ) ⊢ γ → (Γ , γ) ⊢ ψ → (Γ , ϕ) ⊢ ψ
⊢-trans {ϕ} {ψ} {γ} {Γ} Γ,ϕ⊢γ Γ,γ⊢ψ = ∨-elim (Γ , ϕ) γ ψ ψ (∨-introʳ (Γ , ϕ) γ ψ Γ,ϕ⊢γ) (rearrange Γ γ ϕ ψ (ext (Γ , γ) ϕ ψ Γ,γ⊢ψ)) (p∈Γ ((Γ , ϕ) , ψ) ψ Z)

-- [ Γ , ϕ      ⊢ γ ∨ ψ ]:    (∨-introˡ (Γ , ϕ) γ ψ Γ,ϕ⊢γ)
-- [ Γ , ϕ , γ  ⊢ ψ     ]:    (rearrange Γ γ ϕ ψ (ext (Γ , γ) ϕ ψ Γ,γ⊢ψ))
-- [ Γ , ϕ , ψ  ⊢ ψ     ]:    (p∈Γ ((Γ , ϕ) , ψ) ψ Z)
-- [ Γ , ϕ      ⊢ ψ     ]:    ∨-elim (∨-introˡ (Γ , ϕ) ψ Γ,ϕ⊢γ) (ext (Γ , γ) ϕ ψ Γ,γ⊢ψ) (p∈Γ (Γ , ϕ , ψ) ψ S Z)
-------------------------------------------------------------------


∼-trans : ∀ {ϕ ψ γ : Formula} {Γ : ctxt} → Γ ⊢ ϕ ∼ γ → Γ ⊢ γ ∼ ψ → Γ ⊢ ϕ ∼ ψ
∼-trans x y = ⟨ ⊢-trans (×-projₗ x) (×-projₗ y) , ⊢-trans (×-projᵣ y) (×-projᵣ x) ⟩
