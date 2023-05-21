{-# OPTIONS --cubical --safe #-}
module LindenbaumTarski where


open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)

open import Cubical.Relation.Binary.Base

open import Cubical.Data.Nat.Base
open import Cubical.Data.Prod.Base

open import Cubical.Data.Bool.Base

open import Cubical.Algebra.DistLattice.Base



-- Definition: Formula
data Formula : Type where
  const : ℕ      → Formula
  _∧_   : Formula → Formula → Formula
  _∨_   : Formula → Formula → Formula
  ¬_    : Formula → Formula
  ⊥     : Formula
  ⊤     : Formula


infix  35  _∧_
infix  30  _∨_
infixl 36  ¬_
infix  20  _⊢_
infix  23  _∷_
 

-- Definition: Context
data ctxt : Type where
  ∅    : ctxt
  _∷_  : ctxt → Formula → ctxt


-- Definition: Lookup
data _∈_ : Formula → ctxt → Type where
  Z  : ∀ {Γ ϕ}   → ϕ ∈ Γ ∷ ϕ   
  S  : ∀ {Γ ϕ ψ} → ϕ ∈ Γ → ϕ ∈ Γ ∷ ψ


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
      → Γ ∷ ϕ ⊢ γ
      → Γ ∷ ψ ⊢ γ
      → Γ ⊢ γ

  ¬-I : {Γ : ctxt} {ϕ : Formula}
      → Γ ∷ ϕ ⊢ ⊥
      → Γ ⊢ ¬ ϕ
      
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
        
  LEM : {ϕ : Formula}
      → ∅ ⊢ ϕ ∨ ¬ ϕ
  
  weakening : {Γ : ctxt} {ϕ ψ : Formula}
            → Γ ⊢ ψ
            → Γ ∷ ϕ ⊢ ψ
            
  exchange : {Γ : ctxt} {ϕ ψ γ : Formula}
           → (Γ ∷ ϕ) ∷ ψ ⊢ γ
           → (Γ ∷ ψ) ∷ ϕ ⊢ γ
           
--  contraction : {Γ : ctxt} {ϕ ψ : Formula}
--              → (Γ ∷ ϕ) ∷ ϕ ⊢ ψ
--              → (Γ ∷ ϕ) ⊢ ψ



module _ {Γ : ctxt} where

  infixl 25 ¬/_

  ------------------
  -- Usefull lemmas
  ------------------
  superweakening : ∀ {Γ : ctxt} {ϕ : Formula} → ∅ ⊢ ϕ → Γ ⊢ ϕ
  superweakening {∅} x = x
  superweakening {Δ ∷ ψ} x = weakening (superweakening x)

  cut : ∀ {ϕ ψ γ : Formula} → Γ ∷ ϕ ⊢ γ → Γ ∷ γ ⊢ ψ → Γ ∷ ϕ ⊢ ψ
  cut x y = ∨-E (∨-I₂ x) (exchange (weakening y)) (axiom Z)


  ------------------------------------------------------
  -- Defining relation where two formulas are related
  -- if they are provably equivalent. Then proving that
  -- the relation is an equivalence relation by proving
  -- it is reflexive, symmetric and transitive.
  ------------------------------------------------------
  
  _∼_ : Formula → Formula → Type
  ϕ ∼ ψ = Γ ∷ ϕ ⊢ ψ × Γ ∷ ψ ⊢ ϕ

  ∼-refl : ∀ (ϕ : Formula) → ϕ ∼ ϕ
  ∼-refl _ = (axiom Z , axiom Z)

  ∼-sym : ∀ {ϕ ψ : Formula} → ϕ ∼ ψ → ψ ∼ ϕ
  ∼-sym (A , B) = (B , A)

  ∼-trans : ∀ {ϕ ψ γ : Formula} → ϕ ∼ γ → γ ∼ ψ → ϕ ∼ ψ
  ∼-trans (x₁ , x₂) (y₁ , y₂) = (cut x₁ y₁ , cut y₂ x₂)
                              

  ----------------------------------------
  -- Properties of propositional calculus
  ----------------------------------------

  -- Commutativity on ∧
  ∧-comm : ∀ {ϕ ψ : Formula} → Γ ∷ ϕ ∧ ψ ⊢ ψ ∧ ϕ
  ∧-comm = ∧-I (∧-E₂ (axiom Z)) (∧-E₁ (axiom Z))

  ∼-comm-∧ : ∀ {ϕ ψ : Formula} → ϕ ∧ ψ ∼ ψ ∧ ϕ
  ∼-comm-∧ = (∧-comm , ∧-comm)


  -- Commutativity on ∨
  ∨-comm : {ϕ ψ : Formula} → Γ ∷ ϕ ∨ ψ ⊢ ψ ∨ ϕ
  ∨-comm = ∨-E (axiom Z) (∨-I₁ (axiom Z)) (∨-I₂ (axiom Z))

  ∼-comm-∨ : ∀ {ϕ ψ : Formula} → ϕ ∨ ψ ∼ ψ ∨ ϕ
  ∼-comm-∨ = (∨-comm , ∨-comm)


  -- Associativity on ∧
  ∧-ass1 : ∀ {ϕ ψ γ : Formula} → Γ ∷ ϕ ∧ (ψ ∧ γ) ⊢ (ϕ ∧ ψ) ∧ γ
  ∧-ass1 = ∧-I (∧-I (∧-E₁ (axiom Z)) (∧-E₁ (∧-E₂ (axiom Z))))
               (∧-E₂ (∧-E₂ (axiom Z)))
                       
  ∧-ass2 : ∀ {ϕ ψ γ : Formula} → Γ ∷ (ϕ ∧ ψ) ∧ γ ⊢ ϕ ∧ (ψ ∧ γ)
  ∧-ass2 = ∧-I (∧-E₁ (∧-E₁ (axiom Z)))
               (∧-I (∧-E₂ (∧-E₁ (axiom Z)))
                    (∧-E₂ (axiom Z)))

  ∼-ass-∧ : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∧ γ) ∼ (ϕ ∧ ψ) ∧ γ
  ∼-ass-∧ = (∧-ass1 , ∧-ass2)


  -- Associativity on ∨
  ∨-ass1 : ∀ {ϕ ψ γ : Formula} → Γ ∷ ϕ ∨ (ψ ∨ γ) ⊢ (ϕ ∨ ψ) ∨ γ
  ∨-ass1 = ∨-E (axiom Z)
               (∨-I₂ (∨-I₂ (axiom Z)))
               (∨-E (axiom Z)
                    (∨-I₂ (∨-I₁ (axiom Z)))
                    (∨-I₁ (axiom Z)))
                                          
  ∨-ass2 : ∀ {ϕ ψ γ : Formula} → Γ ∷ (ϕ ∨ ψ) ∨ γ ⊢ ϕ ∨ (ψ ∨ γ)
  ∨-ass2 = ∨-E (axiom Z)
               (∨-E (axiom Z)
                    (∨-I₂ (axiom Z))
                    (∨-I₁ (∨-I₂ (axiom Z))))
               (∨-I₁ (∨-I₁ (axiom Z)))

  ∼-ass-∨ : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∨ γ) ∼ (ϕ ∨ ψ) ∨ γ
  ∼-ass-∨ = (∨-ass1 , ∨-ass2)


  -- Distributivity over ∧
  ∧-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ∷ ϕ ∧ (ψ ∨ γ) ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  ∧-dist1 = ∨-E (∧-E₂ (axiom Z))
                (∨-I₂ (∧-I (∧-E₁ (axiom (S Z))) (axiom Z)))
                (∨-I₁ (∧-I (∧-E₁ (axiom (S Z))) (axiom Z)))


  ∧-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ∷ (ϕ ∧ ψ) ∨ (ϕ ∧ γ) ⊢ ϕ ∧ (ψ ∨ γ)
  ∧-dist2 = ∧-I (∨-E (axiom Z)
                     (∧-E₁ (axiom Z))
                     (∧-E₁ (axiom Z)))
                (∨-E (axiom Z)
                     (∨-I₂ (∧-E₂ (axiom Z)))
                     (∨-I₁ (∧-E₂ (axiom Z))))

  ∼-dist-∧ : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∨ γ) ∼ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  ∼-dist-∧ = (∧-dist1 , ∧-dist2)


  -- Distributivity over ∨
  ∨-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ∷ ϕ ∨ (ψ ∧ γ) ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  ∨-dist1 = ∨-E (axiom Z)
                (∧-I (∨-I₂ (axiom Z))
                     (∨-I₂ (axiom Z)))
                (∧-I (∨-I₁ (∧-E₁ (axiom Z)))
                     (∨-I₁ (∧-E₂ (axiom Z))))
  
  ∨-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ∷ (ϕ ∨ ψ) ∧ (ϕ ∨ γ) ⊢ ϕ ∨ (ψ ∧ γ)
  ∨-dist2 = ∨-E (∧-E₁ (axiom Z))
                (∨-I₂ (axiom Z))
                (∨-E (∧-E₂ (axiom (S Z)))
                     (∨-I₂ (axiom Z))
                     (∨-I₁ (∧-I (axiom (S Z)) (axiom Z))))

  ∼-dist-∨ : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∧ γ) ∼ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  ∼-dist-∨ = (∨-dist1 , ∨-dist2)


  ---------------------------------------------------------
  -- Lindenbaum-Tarski algebra is defined as the quotioent
  -- algebra obtained by factoring the algebra of formulas
  -- by the above defined equivalence relation.
  ---------------------------------------------------------
  
  LindenbaumTarski : Type
  LindenbaumTarski = Formula / _∼_


  --------------------------------------------------
  -- The equivalence relation ∼ respects operations
  --------------------------------------------------

  ∼-respects-∧ : ∀ (ϕ ϕ' ψ ψ' : Formula) → ϕ ∼ ϕ' → ψ ∼ ψ' → (ϕ ∧ ψ) ∼ (ϕ' ∧ ψ')
  ∼-respects-∧ ϕ ϕ' ψ ψ' (x₁ , x₂) (y₁ , y₂) = ∧-I (cut (∧-E₁ (axiom Z)) x₁) (cut (∧-E₂ (axiom Z)) y₁) ,
                                               ∧-I (cut (∧-E₁ (axiom Z)) x₂) (cut (∧-E₂ (axiom Z)) y₂)

  ∼-respects-∨ : ∀ (ϕ ϕ' ψ ψ' : Formula) → ϕ ∼ ϕ' → ψ ∼ ψ' → (ϕ ∨ ψ) ∼ (ϕ' ∨ ψ')
  ∼-respects-∨ ϕ ϕ' ψ ψ' (x₁ , x₂) (y₁ , y₂) = ∨-E (axiom Z)
                                                   (∨-I₂ (exchange (weakening x₁)))
                                                   (∨-I₁ (exchange (weakening y₁))) ,
                                               ∨-E (axiom Z)
                                                   (∨-I₂ (exchange (weakening x₂)))
                                                   (∨-I₁ (exchange (weakening y₂)))

  ∼-respects-¬ : ∀ (ϕ ϕ' : Formula) → ϕ ∼ ϕ' → (¬ ϕ) ∼ (¬ ϕ')
  ∼-respects-¬ ϕ ϕ' (x₁ , x₂) = ¬-I (¬-E (exchange (weakening x₂)) (axiom (S Z))) ,
                                ¬-I (¬-E (exchange (weakening x₁)) (axiom (S Z)))


  -------------------------------------------------------------------
  -- Definition: Binary operations and propositional constants in LT
  -------------------------------------------------------------------
  
  _∧/_ : LindenbaumTarski → LindenbaumTarski → LindenbaumTarski
  A ∧/ B = setQuotBinOp ∼-refl ∼-refl _∧_ ∼-respects-∧ A B

  _∨/_ : LindenbaumTarski → LindenbaumTarski → LindenbaumTarski
  A ∨/ B = setQuotBinOp ∼-refl ∼-refl _∨_ ∼-respects-∨ A B

  ¬/_ : LindenbaumTarski → LindenbaumTarski
  ¬/ A = setQuotUnaryOp ¬_ ∼-respects-¬ A
  
  ⊤/ : LindenbaumTarski
  ⊤/ = [ ⊤ ]
  
  ⊥/ : LindenbaumTarski
  ⊥/ = [ ⊥ ]


  -------------------------------------------------------------
  -- By proving the Lindenbaum-Tarski algebra can be viewed as
  -- a complemented distributive lattice, we prove that it is
  -- also a Boolean algebra.
  -------------------------------------------------------------

  LindenbaumTarski-DistLattice : DistLattice _
  LindenbaumTarski-DistLattice = makeDistLattice∧lOver∨l
                                 ⊥/
                                 ⊤/
                                 _∨/_
                                 _∧/_
                                 isSet-LT
                                 ∨/-ass
                                 ∨/-id
                                 ∨/-comm
                                 ∧/-ass
                                 ∧/-id
                                 ∧/-comm
                                 ∧/-abs
                                 ∧/-dist
    where
        isSet-LT : ∀ (A B : LindenbaumTarski) → isProp(A ≡ B)
        isSet-LT A B = squash/ _ _

        ∧/-comm : ∀ (A B : LindenbaumTarski) → A ∧/ B ≡ B ∧/ A
        ∧/-comm = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ∼-comm-∧

        ∨/-comm : ∀ (A B : LindenbaumTarski) → A ∨/ B ≡ B ∨/ A
        ∨/-comm = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ∼-comm-∨

        ∧/-ass : ∀ (A B C : LindenbaumTarski) → A ∧/ (B ∧/ C) ≡ (A ∧/ B) ∧/ C
        ∧/-ass = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ∼-ass-∧

        ∨/-ass : ∀ (A B C : LindenbaumTarski) → A ∨/ (B ∨/ C) ≡ (A ∨/ B) ∨/ C
        ∨/-ass = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ∼-ass-∨

        ∧/-dist : ∀ (A B C : LindenbaumTarski) → A ∧/ (B ∨/ C) ≡ (A ∧/ B) ∨/ (A ∧/ C)
        ∧/-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ∼-dist-∧

        ∨/-dist : ∀ (A B C : LindenbaumTarski) → A ∨/ (B ∧/ C) ≡ (A ∨/ B) ∧/ (A ∨/ C)
        ∨/-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ∼-dist-∨

        ∧/-abs : ∀ (A B : LindenbaumTarski) → A ∧/ (A ∨/ B) ≡ A
        ∧/-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∧-E₁ (axiom Z) , ∧-I (axiom Z) (∨-I₂ (axiom Z)))

        ∨/-abs : ∀ (A B : LindenbaumTarski) → (A ∧/ B) ∨/ B ≡ B
        ∨/-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∨-E (axiom Z) (∧-E₂ (axiom Z)) (axiom Z) , ∨-I₁ (axiom Z))

        ∨/-id : ∀ (A : LindenbaumTarski) → A ∨/ ⊥/ ≡ A
        ∨/-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∨-E (axiom Z) (axiom Z) (⊥-E (axiom Z)) , ∨-I₂ (axiom Z))

        ∧/-id : ∀ (A : LindenbaumTarski) → A ∧/ ⊤/ ≡ A
        ∧/-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∧-E₁ (axiom Z) , ∧-I (axiom Z) (superweakening ⊤-I))



  open DistLatticeStr (snd LindenbaumTarski-DistLattice)

  LindenbaumTarski-DistLattice-supremum : (A : fst LindenbaumTarski-DistLattice) → A ∨l ¬/ A ≡ 1l
  LindenbaumTarski-DistLattice-supremum A = ∨/-comp A
    where
        ∨/-comp : ∀ (A : LindenbaumTarski) → A ∨/ ¬/ A ≡ ⊤/
        ∨/-comp = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (superweakening ⊤-I , superweakening LEM)


  LindenbaumTarski-DistLattice-infimum : (A : fst LindenbaumTarski-DistLattice) → A ∧l ¬/ A ≡ 0l
  LindenbaumTarski-DistLattice-infimum A = ∧/-comp A
    where
        ∧/-comp : ∀ (A : LindenbaumTarski) → A ∧/ ¬/ A ≡ ⊥/
        ∧/-comp = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (¬-E (∧-E₁ (axiom Z)) (∧-E₂ (axiom Z)) , ⊥-E (axiom Z))


  -----------------------------------------------
  -- If ⊢ ϕ then [ϕ] should be the same as ⊤/.
  -- We can view this as a form of soundness.
  -----------------------------------------------

  sound : ∀ {ϕ : Formula} → ∅ ⊢ ϕ → [ ϕ ] ≡ ⊤/
  sound x = eq/ _ _ (superweakening ⊤-I , superweakening x)
