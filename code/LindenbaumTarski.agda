{-# OPTIONS --cubical #-}


module LindenbaumTarski where

open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Nat.Base

data Formula : Type where
  _∧'_    : Formula → Formula → Formula
  _∨'_    : Formula → Formula → Formula
  ¬'_     : Formula → Formula
  const   : ℕ      → Formula
  ⊥'      : Formula
  ⊤'      : Formula


infix 35  _∧'_
infix 30 _∨'_
infixl 36  ¬'_
infix 15 _×_
infix 20 _⊢_
infix 10 _,'_
 

data ctxt : Type where
  ∅ : ctxt
  _,'_ : ctxt → Formula → ctxt

data _∈_ : Formula → ctxt → Type where
  Z : ∀ {Γ ϕ} → ϕ ∈ (Γ ,' ϕ)
  S_ : ∀ {Γ ϕ ψ} → ϕ ∈ Γ → ϕ ∈ (Γ ,' ψ)

data _⊢_ : ctxt → Formula → Type where

  ∧-intro : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ϕ → Γ ⊢ ψ → Γ ⊢ ϕ ∧' ψ
    
  ∧-elimˡ : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ϕ ∧' ψ → Γ ⊢ ϕ
    
  ∧-elimʳ : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ϕ ∧' ψ → Γ ⊢ ψ
  
  ∨-introˡ : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ψ → Γ ⊢ ϕ ∨' ψ
    
  ∨-introʳ : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ϕ → Γ ⊢ ϕ ∨' ψ

  ∨-elim : (Γ : ctxt) (ϕ ψ γ : Formula) → Γ ⊢ ϕ ∨' ψ → (Γ ,' ϕ) ⊢ γ → (Γ ,' ψ) ⊢ γ → Γ ⊢ γ

  ¬-intro : (Γ : ctxt) (ϕ : Formula) → (Γ ,' ϕ) ⊢ ⊥' → Γ ⊢ ¬' ϕ
    
  ⊥-intro : (Γ : ctxt) (ϕ : Formula) → Γ ⊢ ϕ → Γ ⊢ ¬' ϕ → Γ ⊢ ⊥'

  ⊥-elim : (Γ : ctxt) (ϕ : Formula) → (Γ ,' ⊥') ⊢ ϕ

  ⊤-intro : ∅ ⊢ ⊤'

  axiom : (Γ : ctxt) (ϕ : Formula) → ϕ ∈ Γ → Γ ⊢ ϕ

  weakening : (Γ : ctxt) (ϕ ψ : Formula) → Γ ⊢ ψ → (Γ ,' ϕ) ⊢ ψ

  exchange : (Γ : ctxt) (ϕ ψ γ : Formula) → ((Γ ,' ϕ) ,' ψ) ⊢ γ → ((Γ ,' ψ) ,' ϕ) ⊢ γ

  contraction : (Γ : ctxt) (ϕ ψ : Formula) → ((Γ ,' ϕ) ,' ϕ) ⊢ ψ → (Γ ,' ϕ) ⊢ ψ
  

data _×_ (A B : Type) : Type where
  ⟨_,_⟩ : A → B → A × B

×-fst : ∀ {A B : Set} → A × B → A
×-fst ⟨ A , B ⟩ = A

×-snd : ∀ {A B : Set} → A × B → B
×-snd ⟨ A , B ⟩ = B


module _ {Γ : ctxt} where

  infixl 25 ¬/_


  -- Commutativity on ∧ and ∨

  ∧-comm : (ϕ ψ : Formula) → (Γ ,' ϕ ∧' ψ) ⊢ ψ ∧' ϕ
  ∧-comm ϕ ψ = ∧-intro _ _ _ (∧-elimʳ _ _ ψ (axiom _ _ Z)) (∧-elimˡ _ _ ψ (axiom _ _ Z))

  ∨-comm : (ϕ ψ : Formula) → (Γ ,' ϕ ∨' ψ) ⊢ ψ ∨' ϕ
  ∨-comm ϕ ψ = ∨-elim _ ϕ ψ (ψ ∨' ϕ) (axiom _ _ Z) (∨-introˡ _ _ _ (axiom _ _ Z)) (∨-introʳ _ _ _ (axiom _ _ Z))


  -- Associativity on ∧ and ∨
  
  ∧-assoc1 : ∀ (ϕ ψ γ : Formula) → (Γ ,' (ϕ ∧' ψ) ∧' γ) ⊢ ϕ ∧' (ψ ∧' γ)
  ∧-assoc1 ϕ ψ γ = ∧-intro _ _ _ (∧-elimˡ _ _ ψ (∧-elimˡ _ _ γ (axiom _ _ Z)))
                  (∧-intro _ _ _ (∧-elimʳ _ ϕ _ (∧-elimˡ _ _ γ (axiom _ _ Z)))
                                 (∧-elimʳ _ (ϕ ∧' ψ) _ (axiom _ _ Z)))

  ∧-assoc2 : ∀ (ϕ ψ γ : Formula) → (Γ ,' ϕ ∧' (ψ ∧' γ)) ⊢ (ϕ ∧' ψ) ∧' γ
  ∧-assoc2 ϕ ψ γ = ∧-intro _ _ _
                  (∧-intro _ _ _ (∧-elimˡ _ _ (ψ ∧' γ) (axiom _ _ Z))
                                 (∧-elimˡ _ _ γ (∧-elimʳ _ ϕ _ (axiom _ _ Z))))
                                 (∧-elimʳ _ ψ _ (∧-elimʳ _ ϕ _ (axiom _ _ Z)))

  ∨-assoc1 : ∀ (ϕ ψ γ : Formula) → (Γ ,' (ϕ ∨' ψ) ∨' γ) ⊢ ϕ ∨' (ψ ∨' γ)
  ∨-assoc1 ϕ ψ γ = ∨-elim _ (ϕ ∨' ψ) γ (ϕ ∨' (ψ ∨' γ))
                          (axiom _ _ Z)
                          (∨-elim _ ϕ ψ (ϕ ∨' (ψ ∨' γ))
                                  (axiom _ _ Z)
                                  (∨-introʳ _ _ _ (axiom _ _ Z))
                                  (∨-introˡ _ _ _ (∨-introʳ _ _ _ (axiom _ _ Z))))
                          (∨-introˡ _ _ _ (∨-introˡ _ _ _ (axiom _ _ Z)))

  ∨-assoc2 : ∀ (ϕ ψ γ : Formula) → (Γ ,' ϕ ∨' (ψ ∨' γ)) ⊢ (ϕ ∨' ψ) ∨' γ
  ∨-assoc2 ϕ ψ γ = ∨-elim _ ϕ (ψ ∨' γ) ((ϕ ∨' ψ) ∨' γ)
                          (axiom _ _ Z)
                          (∨-introʳ _ _ _ (∨-introʳ _ _ _ (axiom _ _ Z)))
                          (∨-elim _ ψ γ ((ϕ ∨' ψ) ∨' γ)
                                  (axiom _ _ Z)
                                  (∨-introʳ _ _ _ (∨-introˡ _ _ _ (axiom _ _ Z)))
                                  (∨-introˡ _ _ _ (axiom _ _ Z)))


  -- Distributivity over ∧ and ∨

  ∧-dist1 : ∀ (ϕ ψ γ : Formula) → (Γ ,' ϕ ∧' (ψ ∨' γ)) ⊢ (ϕ ∧' ψ) ∨' (ϕ ∧' γ)
  ∧-dist1 ϕ ψ γ = ∨-elim _ ψ γ _
                         (∧-elimʳ _ ϕ _ (axiom _ _ Z))
                         (∨-introʳ _ _ _ (∧-intro _ _ _ (exchange _ _ _ _ (∧-elimˡ _ _ (ψ ∨' γ) (axiom _ _ Z))) (axiom _ _ Z)))
                         (∨-introˡ _ _ _ (∧-intro _ _ _ (exchange _ _ _ _ (∧-elimˡ _ _ (ψ ∨' γ) (axiom _ _ Z))) (axiom _ _ Z)))

  ∧-dist2 : ∀ (ϕ ψ γ : Formula) → (Γ ,' (ϕ ∧' ψ) ∨' (ϕ ∧' γ)) ⊢ ϕ ∧' (ψ ∨' γ)
  ∧-dist2 ϕ ψ γ = ∧-intro _ _ _ (∨-elim _ (ϕ ∧' ψ) (ϕ ∧' γ) ϕ (axiom _ _ Z) (∧-elimˡ _ _ ψ (axiom _ _ Z))
                          (∧-elimˡ _ _ γ (axiom _ _ Z))) (∨-elim _ (ϕ ∧' ψ) (ϕ ∧' γ) _ (axiom _ _ Z)
                          (∨-introʳ _ _ _ (∧-elimʳ _ ϕ _ (axiom _ _ Z))) (∨-introˡ _ _ _ (∧-elimʳ _ ϕ γ (axiom _ _ Z))))

  ∨-dist1 : ∀ (ϕ ψ γ : Formula) → (Γ ,' ϕ ∨' (ψ ∧' γ)) ⊢ (ϕ ∨' ψ) ∧' (ϕ ∨' γ)
  ∨-dist1 ϕ ψ γ = ∨-elim _ ϕ (ψ ∧' γ) ((ϕ ∨' ψ) ∧' (ϕ ∨' γ))
                         (axiom _ _ Z)
                         (∧-intro _ _ _ (∨-introʳ _ _ _ (axiom _ _ Z)) (∨-introʳ _ _ _ (axiom _ _ Z)))
                         (∧-intro _ _ _ (∨-introˡ _ _ _ (∧-elimˡ _ _ γ (axiom _ _ Z))) (∨-introˡ _ _ _ (∧-elimʳ _ ψ _ (axiom _ _ Z))))

  ∨-dist2 : ∀ (ϕ ψ γ : Formula) → (Γ ,' (ϕ ∨' ψ) ∧' (ϕ ∨' γ)) ⊢ ϕ ∨' (ψ ∧' γ)
  ∨-dist2 ϕ ψ γ = ∨-elim _ ϕ ψ (ϕ ∨' (ψ ∧' γ))
                         (∧-elimˡ _ _ (ϕ ∨' γ) (axiom _ _ Z))
                         (∨-elim _ ϕ γ _
                                 (∨-introʳ _ _ _ (axiom _ _ Z))
                                 (∨-introʳ _ _ _ (axiom _ _ Z))
                                 (exchange _ _ _ _ (∨-introʳ _ _ _ (axiom _ _ Z))))
                         (∨-elim _ ϕ γ _
                                 (exchange _ _ _ _ (∧-elimʳ _ (ϕ ∨' ψ) _ (axiom _ _ Z)))
                                 (∨-introʳ _ _ _ (axiom _ _ Z))
                                 (∨-introˡ _ _ _ (∧-intro _ _ _ (exchange _ _ _ _ (axiom _ _ Z)) (axiom _ _ Z))))


  -- Equivalence relation
  
  _∼_ : Formula → Formula → Type
  ϕ ∼ ψ = (Γ ,' ϕ) ⊢ ψ × (Γ ,' ψ) ⊢ ϕ

  ∼-refl : ∀ (ϕ : Formula) → ϕ ∼ ϕ
  ∼-refl _ = ⟨ axiom (_ ,' _) _ Z , (axiom (_ ,' _) _ Z) ⟩

  ∼-sym : ∀ {ϕ ψ : Formula} → ϕ ∼ ψ → ψ ∼ ϕ
  ∼-sym ⟨ A , B ⟩ = ⟨ B , A ⟩

  lemma : ∀ {ϕ ψ γ : Formula} → (Γ ,' ϕ) ⊢ γ → (Γ ,' γ) ⊢ ψ → (Γ ,' ϕ) ⊢ ψ
  lemma A B = ∨-elim (_ ,' _) _ _ _ (∨-introʳ (_ ,' _) _ _ A) (exchange _ _ _ _ (weakening (_ ,' _) _ _ B)) (axiom ((_ ,' _) ,' _) _ Z)

  ∼-trans : ∀ {ϕ ψ γ : Formula} → ϕ ∼ γ → γ ∼ ψ → ϕ ∼ ψ
  ∼-trans x y = ⟨ lemma (×-fst x) (×-fst y) , lemma (×-snd y) (×-snd x) ⟩



  -- Lindenbaum-Tarski algebra

  LT : Type
  LT = Formula / _∼_


  -- Binary operations and propositional constants

  lemma2 : (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∧' b) ∼ (a' ∧' b')
  lemma2 a a' b b' x y = ⟨ ∧-intro _ a' b'
                                   (lemma (∧-elimˡ _ _ _  (axiom _ (a ∧' b)    Z)) (×-fst x))
                                   (lemma (∧-elimʳ _ a _  (axiom _ (a ∧' b)    Z)) (×-fst y)) ,
                           ∧-intro _ a b
                                   (lemma (∧-elimˡ _ _ _  (axiom _ (a' ∧' b')  Z)) (×-snd x))
                                   (lemma (∧-elimʳ _ a' _ (axiom _ (a' ∧' b')  Z)) (×-snd y)) ⟩

  lemma3 : (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∨' b) ∼ (a' ∨' b')
  lemma3 a a' b b' x y = ⟨ ∨-elim _ a b (a' ∨' b')
                                  (axiom _ _ Z)
                                  (exchange _ _ _ _ (weakening _ _ _ (∨-introʳ _ _ _ (×-fst x))))
                                  (exchange _ _ _ _ (weakening _ _ _ (∨-introˡ _ _ _ (×-fst y)))) ,
                          ∨-elim _ a' b' (a ∨' b)
                                  (axiom _ _ Z)
                                  (exchange _ _ _ _ (weakening _ _ _ (∨-introʳ _ _ _ (×-snd x))))
                                  (exchange _ _ _ _ (weakening _ _ _ (∨-introˡ _ _ _ (×-snd y)))) ⟩

  lemma4 : (a a' : Formula) → a ∼ a' → (¬' a) ∼ (¬' a')
  lemma4 a a' x = ⟨ ¬-intro _ _ (⊥-intro _ a (exchange _ _ _ _ (weakening _ _ _ (×-snd x))) (weakening _ _ _ (axiom _ _ Z))),
                    ¬-intro _ _ (⊥-intro _ a' (exchange _ _ _ _ (weakening _ _ _ (×-fst x))) (weakening _ _ _ (axiom _ _ Z))) ⟩

  _⋀_ : LT → LT → LT
  A ⋀ B = setQuotBinOp ∼-refl ∼-refl _∧'_ lemma2 A B

  _⋁_ : LT → LT → LT
  A ⋁ B = setQuotBinOp ∼-refl ∼-refl _∨'_ lemma3 A B
  
  ¬/_ : LT → LT
  ¬/ A = setQuotUnaryOp ¬'_ lemma4 A

  ⊤/ : LT
  ⊤/ = [ ⊤' ]
  
  ⊥/ : LT
  ⊥/ = [ ⊥' ]


  -- Commutativity

  ⋀-comm : ∀ (A B : LT) → A ⋀ B ≡ B ⋀ A
  ⋀-comm = elimProp2 (λ _ _ → squash/ _ _) λ ϕ ψ → eq/ _ _ (∼-sym ⟨ (∧-comm ψ ϕ) , ∧-comm ϕ ψ ⟩)

  ⋁-comm : ∀ (A B : LT) → A ⋁ B ≡ B ⋁ A
  ⋁-comm = elimProp2 (λ _ _ → squash/ _ _) λ ϕ ψ → eq/ _ _ (∼-sym ⟨ ∨-comm ψ ϕ , ∨-comm ϕ ψ ⟩)


  -- Associativity
  
  ⋀-assoc : ∀ (A B C : LT) → (A ⋀ B) ⋀ C ≡ A ⋀ (B ⋀ C)
  ⋀-assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ⟨ ∧-assoc1 _ _ _ , ∧-assoc2 _ _ _ ⟩

  ⋁-assoc : ∀ (A B C : LT) → (A ⋁ B) ⋁ C ≡ A ⋁ (B ⋁ C)
  ⋁-assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ⟨ ∨-assoc1 _ _ _ , ∨-assoc2 _ _ _ ⟩


  -- Distributivity

  ⋀-dist : ∀ (A B C : LT) → A ⋀ (B ⋁ C) ≡ (A ⋀ B) ⋁ (A ⋀ C)
  ⋀-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ⟨ ∧-dist1 _ _ _ , ∧-dist2 _ _ _ ⟩

  ⋁-dist : ∀ (A B C : LT) → A ⋁ (B ⋀ C) ≡ (A ⋁ B) ⋀ (A ⋁ C)
  ⋁-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ⟨ ∨-dist1 _ _ _ , ∨-dist2 _ _ _ ⟩


  -- Complement

  ⋀-comp : ∀ (A : LT) → A ⋀ ¬/ A ≡ ⊥/
  ⋀-comp = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _
         ⟨ (⊥-intro _ _ (∧-elimˡ _ _ _ (axiom _ _ Z)) (∧-elimʳ _ _ _ (axiom _ _ Z))) , ⊥-elim _ _ ⟩

  ⋁-comp : ∀ (A : LT) → A ⋁ ¬/ A ≡ ⊤/
  ⋁-comp = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ⟨ weakening _ _ _ {!!} , {!!} ⟩

  -- Absorbtion

  ⋀-abs : ∀ (A B : LT) → (A ⋁ B) ⋀ B ≡ B
  ⋀-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _
        ⟨ (∧-elimʳ _ _ _ (axiom _ _ Z)) , ∧-intro _ _ _ (∨-introˡ _ _ _ (axiom _ _ Z)) (axiom _ _ Z) ⟩

  ⋁-abs : ∀ (A B : LT) → (A ⋀ B) ⋁ B ≡ B
  ⋁-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _
        ⟨ ∨-elim _ _ _ _ (axiom _ _ Z) (∧-elimʳ _ _ _ (axiom _ _ Z)) (axiom _ _ Z) , ∨-introˡ _ _ _ (axiom _ _ Z) ⟩
