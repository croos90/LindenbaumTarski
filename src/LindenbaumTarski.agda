{-# OPTIONS --cubical --safe #-}
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

  ¬-I : {Γ : ctxt} {ϕ : Formula}
      → Γ ∶ ϕ ⊢ ⊥
      → Γ ⊢ ¬ ϕ
      
  ¬-E : {Γ : ctxt} {ϕ : Formula}
      → Γ ⊢ ϕ
      → Γ ⊢ ¬ ϕ
      → Γ ⊢ ⊥
  
  ⊥-E : {Γ : ctxt} {ϕ : Formula}
      → Γ ⊢ ⊥
      → Γ ⊢ ϕ  
  
  ⊤-I : {Γ : ctxt} → Γ ⊢ ⊤
  
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
           
--  contraction : {Γ : ctxt} {ϕ ψ : Formula}
--              → ((Γ ∶ ϕ) ∶ ϕ) ⊢ ψ
--              → (Γ ∶ ϕ) ⊢ ψ


module _ {Γ : ctxt} where

  infixl 25 ¬/_

  ------------------------------------------------------
  -- Defining relation where two formulas are related
  -- if they are provably equivalent. Then proving that
  -- the relation is an equivalence relation by proving
  -- it is reflexive, symmetric and transitive.
  ------------------------------------------------------
  
  _∼_ : Formula → Formula → Type
  ϕ ∼ ψ = Γ ∶ ϕ ⊢ ψ × Γ ∶ ψ ⊢ ϕ

  ∼-refl : ∀ (ϕ : Formula) → ϕ ∼ ϕ
  ∼-refl _ = axiom Z , (axiom Z)
  
  ∼-sym : ∀ {ϕ ψ : Formula} → ϕ ∼ ψ → ψ ∼ ϕ
  ∼-sym (A , B) = B , A

  ⊢trans : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ⊢ γ → Γ ∶ γ ⊢ ψ → Γ ∶ ϕ ⊢ ψ
  ⊢trans A B = ∨-E (∨-I₂ A) (exchange (weakening B)) (axiom Z)

  ∼-trans : ∀ {ϕ ψ γ : Formula} → ϕ ∼ γ → γ ∼ ψ → ϕ ∼ ψ
  ∼-trans x y = ⊢trans (proj₁ x) (proj₁ y) , ⊢trans (proj₂ y) (proj₂ x)


  ----------------------------------------
  -- Properties of propositional calculus
  ----------------------------------------

  -- Commutativity on ∧
  ∧-comm : ∀ {ϕ ψ : Formula} → Γ ∶ ϕ ∧ ψ ⊢ ψ ∧ ϕ
  ∧-comm = ∧-I (∧-E₂ (axiom Z)) (∧-E₁ (axiom Z))

  ∼-comm-∧ : ∀ {ϕ ψ : Formula} → ϕ ∧ ψ ∼ ψ ∧ ϕ
  ∼-comm-∧ = ∧-comm , ∧-comm
  

  -- Commutativity on ∨
  ∨-comm : {ϕ ψ : Formula} → Γ ∶ ϕ ∨ ψ ⊢ ψ ∨ ϕ
  ∨-comm = ∨-E (axiom Z) (∨-I₁ (axiom Z)) (∨-I₂ (axiom Z))

  ∼-comm-∨ : ∀ {ϕ ψ : Formula} → ϕ ∨ ψ ∼ ψ ∨ ϕ
  ∼-comm-∨ = ∨-comm , ∨-comm
  

  -- Associativity on ∧
  ∧-ass1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∧ (ψ ∧ γ) ⊢ (ϕ ∧ ψ) ∧ γ
  ∧-ass1 = ∧-I (∧-I (∧-E₁ (axiom Z)) (∧-E₁ (∧-E₂ (axiom Z))))
               (∧-E₂ (∧-E₂ (axiom Z)))
                       
  ∧-ass2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∧ ψ) ∧ γ ⊢ ϕ ∧ (ψ ∧ γ)
  ∧-ass2 = ∧-I (∧-E₁ (∧-E₁ (axiom Z)))
               (∧-I (∧-E₂ (∧-E₁ (axiom Z)))
                    (∧-E₂ (axiom Z)))

  ∼-ass-∧ : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∧ γ) ∼ (ϕ ∧ ψ) ∧ γ
  ∼-ass-∧ = ∧-ass1 , ∧-ass2


  -- Associativity on ∨
  ∨-ass1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∨ (ψ ∨ γ) ⊢ (ϕ ∨ ψ) ∨ γ
  ∨-ass1 = ∨-E (axiom Z)
                 (∨-I₂ (∨-I₂ (axiom Z)))
                 (∨-E (axiom Z)
                      (∨-I₂ (∨-I₁ (axiom Z)))
                      (∨-I₁ (axiom Z)))
                                          
  ∨-ass2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∨ ψ) ∨ γ ⊢ ϕ ∨ (ψ ∨ γ)
  ∨-ass2 = ∨-E (axiom Z)
                 (∨-E (axiom Z)
                      (∨-I₂ (axiom Z))
                      (∨-I₁ (∨-I₂ (axiom Z))))
                 (∨-I₁ (∨-I₁ (axiom Z)))

  ∼-ass-∨ : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∨ γ) ∼ (ϕ ∨ ψ) ∨ γ
  ∼-ass-∨ = ∨-ass1 , ∨-ass2


  -- Distributivity over ∧
  ∧-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∧ (ψ ∨ γ) ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  ∧-dist1 = ∨-E (∧-E₂ (axiom Z))
                (∨-I₂ (∧-I (weakening (∧-E₁ (axiom Z))) (axiom Z)))
                (∨-I₁ (∧-I (weakening (∧-E₁ (axiom Z))) (axiom Z)))

  ∧-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∧ ψ) ∨ (ϕ ∧ γ) ⊢ ϕ ∧ (ψ ∨ γ)
  ∧-dist2 = ∧-I (∨-E (axiom Z)
                     (∧-E₁ (axiom Z))
                     (∧-E₁ (axiom Z)))
                (∨-E (axiom Z)
                     (∨-I₂ (∧-E₂ (axiom Z)))
                     (∨-I₁ (∧-E₂ (axiom Z))))

  ∼-dist-∧ : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∨ γ) ∼ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  ∼-dist-∧ = ∧-dist1 , ∧-dist2


  -- Distributivity over ∨
  ∨-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∨ (ψ ∧ γ) ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  ∨-dist1 = ∨-E (axiom Z)
                (∧-I (∨-I₂ (axiom Z))
                     (∨-I₂ (axiom Z)))
                (∧-I (∨-I₁ (∧-E₁ (axiom Z)))
                     (∨-I₁ (∧-E₂ (axiom Z))))
  
  ∨-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∨ ψ) ∧ (ϕ ∨ γ) ⊢ ϕ ∨ (ψ ∧ γ)
  ∨-dist2 = ∨-E (∧-E₁ (axiom Z))
                (∨-I₂ (axiom Z))
                (∨-E (∧-E₂ (weakening (axiom Z)))
                     (∨-I₂ (axiom Z))
                     (∨-I₁ (∧-I (weakening (axiom Z)) (axiom Z))))

  ∼-dist-∨ : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∧ γ) ∼ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  ∼-dist-∨ = ∨-dist1 , ∨-dist2


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

  ∼-respects-∧ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∧ b) ∼ (a' ∧ b')
  ∼-respects-∧ a a' b b' x y = ∧-I (⊢trans (∧-E₁ (axiom Z)) (proj₁ x))
                                   (⊢trans (∧-E₂ (axiom Z)) (proj₁ y)) ,
                               ∧-I (⊢trans (∧-E₁ (axiom Z)) (proj₂ x))
                                   (⊢trans (∧-E₂ (axiom Z)) (proj₂ y))

  ∼-respects-∨ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∨ b) ∼ (a' ∨ b')
  ∼-respects-∨ a a' b b' x y = ∨-E (axiom Z)
                                   (exchange (weakening (∨-I₂ (proj₁ x))))
                                   (exchange (weakening (∨-I₁ (proj₁ y)))) ,
                               ∨-E (axiom Z)
                                   (exchange (weakening (∨-I₂ (proj₂ x))))
                                   (exchange (weakening (∨-I₁ (proj₂ y))))

  ∼-respects-¬ : ∀ (a a' : Formula) → a ∼ a' → (¬ a) ∼ (¬ a')
  ∼-respects-¬ a a' x = ¬-I (¬-E (exchange (weakening (proj₂ x))) (weakening (axiom Z))) ,
                        ¬-I (¬-E (exchange (weakening (proj₁ x))) (weakening (axiom Z)))


  -------------------------------------------------------------------
  -- Definition: Binary operations and propositional constants in LT
  -------------------------------------------------------------------
  
  _∧/_ : LindenbaumTarski → LindenbaumTarski → LindenbaumTarski
  A ∧/ B = setQuotBinOp ∼-refl ∼-refl _∧_ ∼-respects-∧ A B

  _∨/_ : LindenbaumTarski  → LindenbaumTarski → LindenbaumTarski
  A ∨/ B = setQuotBinOp ∼-refl ∼-refl _∨_ ∼-respects-∨ A B

  ¬/_ : LindenbaumTarski → LindenbaumTarski
  ¬/ A = setQuotUnaryOp ¬_ ∼-respects-¬ A
  
  ⊤/ : LindenbaumTarski
  ⊤/ = [ ⊤ ]
  
  ⊥/ : LindenbaumTarski
  ⊥/ = [ ⊥ ]


  ------------------------------------------------------------
  -- If ϕ is provable in Γ then [ϕ] should be the same as ⊤/.
  -- We can view this as a form of soundness.
  ------------------------------------------------------------
  
  sound : ∀ {ϕ : Formula} → Γ ⊢ ϕ → [ ϕ ] ≡ ⊤/
  sound x = eq/ _ _ (⊤-I , weakening x)


  -------------------------------------------------------------
  -- By proving the Lindenbaum-Tarski algebra can be viewed as
  -- a complemented distributive lattice, we prove that it is
  -- also boolean.
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
        ∧/-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∧-E₁ (axiom Z) , ∧-I (axiom Z) ⊤-I)


  
  open DistLatticeStr (snd LindenbaumTarski-DistLattice)

  LindenbaumTarski-DistLattice-supremum : (x : fst LindenbaumTarski-DistLattice) → x ∨l ¬/ x ≡ 1l
  LindenbaumTarski-DistLattice-supremum x = ∨/-comp x
    where
        ∨/-comp : ∀ (A : LindenbaumTarski) → A ∨/ ¬/ A ≡ ⊤/
        ∨/-comp = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (⊤-I , LEM)


  LindenbaumTarski-DistLattice-infimum : (x : fst LindenbaumTarski-DistLattice) → x ∧l ¬/ x ≡ 0l
  LindenbaumTarski-DistLattice-infimum x = ∧/-comp x
    where
        ∧/-comp : ∀ (A : LindenbaumTarski) → A ∧/ ¬/ A ≡ ⊥/
        ∧/-comp = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (¬-E (∧-E₁ (axiom Z)) (∧-E₂ (axiom Z)) , ⊥-E (axiom Z))
