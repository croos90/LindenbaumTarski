%<*src>
\begin{code}
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
\end{code}
%<*form>
\begin{code}
data Formula : Type where
  _∧_   : Formula → Formula → Formula
  _∨_   : Formula → Formula → Formula
  ¬_    : Formula → Formula
  const : ℕ      → Formula
  ⊥     : Formula
  ⊤     : Formula
\end{code}
%</form>

%<*infix>
\begin{code}
infix  35  _∧_
infix  30  _∨_
infixl 36  ¬_
infix  20  _⊢_
infix  23  _∶_
\end{code}
%</infix>
\begin{code}
-- Definition: Context
\end{code}
%<*ctxt>
\begin{code}
data ctxt : Type where
  ∅    : ctxt
  _∶_  : ctxt → Formula → ctxt
\end{code}
%</ctxt>

\begin{code}
-- Definition: Lookup
\end{code}

%<*lookup>
\begin{code}
data _∈_ : Formula → ctxt → Type where
  Z  : ∀ {Γ ϕ}   → ϕ ∈ Γ ∶ ϕ
  S  : ∀ {Γ ϕ ψ} → ϕ ∈ Γ → ϕ ∈ Γ ∶ ψ
\end{code}
%</lookup>

\begin{code}
-- Definition: Provability
\end{code}

%<*provability>
\begin{code}
data _⊢_ : ctxt → Formula → Type where
\end{code}
%</provability>

%<*conjI>
\begin{code}
  ∧-I : {Γ : ctxt} {ϕ ψ : Formula}
      → Γ ⊢ ϕ
      → Γ ⊢ ψ
      → Γ ⊢ ϕ ∧ ψ
\end{code}
%</conjI>

%<*conjE1>
\begin{code}
  ∧-E₁ : {Γ : ctxt} {ϕ ψ : Formula}
       → Γ ⊢ ϕ ∧ ψ
       → Γ ⊢ ϕ
\end{code}
%</conjE1>

%<*conjE2>
\begin{code}
  ∧-E₂ : {Γ : ctxt} {ϕ ψ : Formula}
       → Γ ⊢ ϕ ∧ ψ
       → Γ ⊢ ψ
\end{code}
%</conjE2>

%<*disjI1>
\begin{code}
  ∨-I₁ : {Γ : ctxt} {ϕ ψ : Formula}
       → Γ ⊢ ψ
       → Γ ⊢ ϕ ∨ ψ
\end{code}
%</disjI1>

%<*disjI2>
\begin{code}
  ∨-I₂ : {Γ : ctxt} {ϕ ψ : Formula}
       → Γ ⊢ ϕ
       → Γ ⊢ ϕ ∨ ψ
\end{code}
%</disjI2>

%<*disjE>
\begin{code}       
  ∨-E : {Γ : ctxt} {ϕ ψ γ : Formula}
      → Γ ⊢ ϕ ∨ ψ
      → Γ ∶ ϕ ⊢ γ
      → Γ ∶ ψ ⊢ γ
      → Γ ⊢ γ
\end{code}
%</disjE>

%<*negI>
\begin{code}
  ¬-I : {Γ : ctxt} {ϕ : Formula}
      → Γ ∶ ϕ ⊢ ⊥
      → Γ ⊢ ¬ ϕ
\end{code}
%</negI>

%<*negE>
\begin{code}
  ¬-E : {Γ : ctxt} {ϕ : Formula}
      → Γ ⊢ ϕ
      → Γ ⊢ ¬ ϕ
      → Γ ⊢ ⊥
\end{code}
%</negE>

%<*botE>
\begin{code}  
  ⊥-E : {Γ : ctxt} {ϕ : Formula}
      → Γ ⊢ ⊥
      → Γ ⊢ ϕ  
\end{code}
%</botE>

%<*topI>
\begin{code}
  ⊤-I : {Γ : ctxt} → Γ ⊢ ⊤
\end{code}
%</topI>

%<*axiom>
\begin{code}
  axiom : {Γ : ctxt} {ϕ : Formula}
        → ϕ ∈ Γ
        → Γ ⊢ ϕ
\end{code}
%</axiom>

%<*LEM>
\begin{code}
  LEM : {Γ : ctxt} {ϕ : Formula}
      → Γ ⊢ ϕ ∨ ¬ ϕ
\end{code}
%</LEM>

%<*weakening>
\begin{code}
  weakening : {Γ : ctxt} {ϕ ψ : Formula}
            → Γ ⊢ ψ
            → Γ ∶ ϕ ⊢ ψ
\end{code}
%</weakening>

%<*exchange>
\begin{code}
  exchange : {Γ : ctxt} {ϕ ψ γ : Formula}
           → (Γ ∶ ϕ) ∶ ψ ⊢ γ
           → (Γ ∶ ψ) ∶ ϕ ⊢ γ
\end{code}
%</exchange>

\begin{code}
--  contraction : {Γ : ctxt} {ϕ ψ : Formula}
--              → ((Γ ∶ ϕ) ∶ ϕ) ⊢ ψ
--              → (Γ ∶ ϕ) ⊢ ψ
\end{code}

\begin{code}
module _ {Γ : ctxt} where

  infixl 25 ¬/_


  ------------------------------------------------------
  -- Defining relation where two formulas are related
  -- if they are provably equivalent. Then proving that
  -- the relation is an equivalence relation by proving
  -- it is reflexive, symmetric and transitive.
  ------------------------------------------------------
\end{code}

%<*eq>
\begin{code}
  _∼_ : Formula → Formula → Type
  ϕ ∼ ψ = Γ ∶ ϕ ⊢ ψ × Γ ∶ ψ ⊢ ϕ
\end{code}
%</eq>

%<*refl>
\begin{code}
  ∼-refl : ∀ (ϕ : Formula) → ϕ ∼ ϕ
  ∼-refl _ = axiom Z , (axiom Z)
\end{code}
%</refl>

%<*sym>
\begin{code}
  ∼-sym : ∀ {ϕ ψ : Formula} → ϕ ∼ ψ → ψ ∼ ϕ
  ∼-sym (A , B) = B , A
\end{code}
%</sym>

%<*trans-lemma>
\begin{code}
  ⊢trans : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ⊢ γ → Γ ∶ γ ⊢ ψ → Γ ∶ ϕ ⊢ ψ
  ⊢trans A B = ∨-E (∨-I₂ A) (exchange (weakening B)) (axiom Z)
\end{code}
%</trans-lemma>

%<*trans>
\begin{code}
  ∼-trans : ∀ {ϕ ψ γ : Formula} → ϕ ∼ γ → γ ∼ ψ → ϕ ∼ ψ
  ∼-trans x y = ⊢trans (proj₁ x) (proj₁ y) , ⊢trans (proj₂ y) (proj₂ x)
\end{code}
%</trans>

\begin{code}
  ----------------------------------------
  -- Properties of propositional calculus
  ----------------------------------------
\end{code}
\begin{code}
  -- Commutativity on ∧
\end{code}

%<*conj-comm>
\begin{code}
  ∧-comm : ∀ {ϕ ψ : Formula} → Γ ∶ ϕ ∧ ψ ⊢ ψ ∧ ϕ
  ∧-comm = ∧-I (∧-E₂ (axiom Z)) (∧-E₁ (axiom Z))
\end{code}
%</conj-comm>

%<*comm-eq-conj>
\begin{code}
  ∼-comm-∧ : ∀ {ϕ ψ : Formula} → ϕ ∧ ψ ∼ ψ ∧ ϕ
  ∼-comm-∧ = ∧-comm , ∧-comm
\end{code}
%</comm-eq-conj>

\begin{code}
  -- Commutativity on ∨
\end{code}

%<*disj-comm>
\begin{code}
  ∨-comm : {ϕ ψ : Formula} → Γ ∶ ϕ ∨ ψ ⊢ ψ ∨ ϕ
  ∨-comm = ∨-E (axiom Z) (∨-I₁ (axiom Z)) (∨-I₂ (axiom Z))
\end{code}
%</disj-comm>

%<*comm-eq-disj>
\begin{code}
  ∼-comm-∨ : ∀ {ϕ ψ : Formula} → ϕ ∨ ψ ∼ ψ ∨ ϕ
  ∼-comm-∨ = ∨-comm , ∨-comm
\end{code}
%</comm-eq-disj>

\begin{code}
  -- Associativity on ∧
\end{code}

%<*conj-ass1>
\begin{code}
  ∧-ass1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∧ (ψ ∧ γ) ⊢ (ϕ ∧ ψ) ∧ γ
  ∧-ass1 = ∧-I (∧-I (∧-E₁ (axiom Z)) (∧-E₁ (∧-E₂ (axiom Z))))
               (∧-E₂ (∧-E₂ (axiom Z)))
\end{code}
%</conj-ass1>

%<*conj-ass2>
\begin{code}
  ∧-ass2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∧ ψ) ∧ γ ⊢ ϕ ∧ (ψ ∧ γ)
  ∧-ass2 = ∧-I (∧-E₁ (∧-E₁ (axiom Z)))
               (∧-I (∧-E₂ (∧-E₁ (axiom Z)))
                    (∧-E₂ (axiom Z)))
\end{code}
%</conj-ass2>

%<*ass-eq-conj>
\begin{code}
  ∼-ass-∧ : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∧ γ) ∼ (ϕ ∧ ψ) ∧ γ
  ∼-ass-∧ = ∧-ass1 , ∧-ass2
\end{code}
%</ass-eq-conj>

\begin{code}
  -- Associativity on ∨
\end{code}

%<*disj-ass1>
\begin{code}
  ∨-ass1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∨ (ψ ∨ γ) ⊢ (ϕ ∨ ψ) ∨ γ
  ∨-ass1 = ∨-E (axiom Z)
                 (∨-I₂ (∨-I₂ (axiom Z)))
                 (∨-E (axiom Z)
                      (∨-I₂ (∨-I₁ (axiom Z)))
                      (∨-I₁ (axiom Z)))
\end{code}
%</disj-ass1>

%<*disj-ass2>
\begin{code}
  ∨-ass2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∨ ψ) ∨ γ ⊢ ϕ ∨ (ψ ∨ γ)
  ∨-ass2 = ∨-E (axiom Z)
                 (∨-E (axiom Z)
                      (∨-I₂ (axiom Z))
                      (∨-I₁ (∨-I₂ (axiom Z))))
                 (∨-I₁ (∨-I₁ (axiom Z)))
\end{code}
%</disj-ass2>

%<*ass-eq-disj>
\begin{code}
  ∼-ass-∨ : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∨ γ) ∼ (ϕ ∨ ψ) ∨ γ
  ∼-ass-∨ = ∨-ass1 , ∨-ass2
\end{code}
%</ass-eq-disj>

\begin{code}
  -- Distributivity over ∧
\end{code}

%<*conj-dist1>
\begin{code}
  ∧-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∧ (ψ ∨ γ) ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  ∧-dist1 = ∨-E (∧-E₂ (axiom Z))
                (∨-I₂ (∧-I (weakening (∧-E₁ (axiom Z))) (axiom Z)))
                (∨-I₁ (∧-I (weakening (∧-E₁ (axiom Z))) (axiom Z)))
\end{code}
%</conj-dist1>

%<*conj-dist2>
\begin{code}
  ∧-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∧ ψ) ∨ (ϕ ∧ γ) ⊢ ϕ ∧ (ψ ∨ γ)
  ∧-dist2 = ∧-I (∨-E (axiom Z)
                     (∧-E₁ (axiom Z))
                     (∧-E₁ (axiom Z)))
                (∨-E (axiom Z)
                     (∨-I₂ (∧-E₂ (axiom Z)))
                     (∨-I₁ (∧-E₂ (axiom Z))))
\end{code}
%</conj-dist2>

%<*dist-eq-conj>
\begin{code}
  ∼-dist-∧ : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∨ γ) ∼ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  ∼-dist-∧ = ∧-dist1 , ∧-dist2
\end{code}
%</dist-eq-conj>

\begin{code}
  -- Distributivity over ∨
\end{code}

%<*disj-dist1>
\begin{code}
  ∨-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∨ (ψ ∧ γ) ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  ∨-dist1 = ∨-E (axiom Z)
                (∧-I (∨-I₂ (axiom Z))
                     (∨-I₂ (axiom Z)))
                (∧-I (∨-I₁ (∧-E₁ (axiom Z)))
                     (∨-I₁ (∧-E₂ (axiom Z))))
\end{code}
%</disj-dist1>

%<*disj-dist2>
\begin{code}
  ∨-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∨ ψ) ∧ (ϕ ∨ γ) ⊢ ϕ ∨ (ψ ∧ γ)
  ∨-dist2 = ∨-E (∧-E₁ (axiom Z))
                (∨-I₂ (axiom Z))
                (∨-E (∧-E₂ (weakening (axiom Z)))
                     (∨-I₂ (axiom Z))
                     (∨-I₁ (∧-I (weakening (axiom Z)) (axiom Z))))
\end{code}
%</disj-dist2>

%<*dist-eq-disj>
\begin{code}
  ∼-dist-∨ : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∧ γ) ∼ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  ∼-dist-∨ = ∨-dist1 , ∨-dist2
\end{code}
%</dist-eq-disj>

\begin{code}
  ---------------------------------------------------------
  -- Lindenbaum-Tarski algebra is defined as the quotioent
  -- algebra obtained by factoring the algebra of formulas
  -- by the above defined equivalence relation.
  ---------------------------------------------------------
\end{code}

%<*LT>
\begin{code}
  LindenbaumTarski : Type
  LindenbaumTarski = Formula / _∼_
\end{code}
%</LT>

\begin{code}
  --------------------------------------------------
  -- The equivalence relation ∼ respects operations
  --------------------------------------------------
\end{code}

%<*eq-respects-conj>
\begin{code}
  ∼-respects-∧ : ∀ (a a' b b' : Formula) 
               → a ∼ a' 
               → b ∼ b' 
               → (a ∧ b) ∼ (a' ∧ b')
  ∼-respects-∧ a a' b b' x y = 
               ∧-I (⊢trans (∧-E₁ (axiom Z)) (proj₁ x))
                   (⊢trans (∧-E₂ (axiom Z)) (proj₁ y)) ,
               ∧-I (⊢trans (∧-E₁ (axiom Z)) (proj₂ x))
                   (⊢trans (∧-E₂ (axiom Z)) (proj₂ y))
\end{code}
%</eq-respects-conj>

%<*eq-respects-disj>
\begin{code}
  ∼-respects-∨ : ∀ (a a' b b' : Formula) 
               → a ∼ a' 
               → b ∼ b' 
               → (a ∨ b) ∼ (a' ∨ b')
  ∼-respects-∨ a a' b b' x y = 
               ∨-E (axiom Z)
                   (exchange (weakening (∨-I₂ (proj₁ x))))
                   (exchange (weakening (∨-I₁ (proj₁ y)))) ,
               ∨-E (axiom Z)
                   (exchange (weakening (∨-I₂ (proj₂ x))))
                   (exchange (weakening (∨-I₁ (proj₂ y))))
\end{code}
%</eq-respects-disj>

%<*eq-respects-neg>
\begin{code}
  ∼-respects-¬ : ∀ (a a' : Formula) 
               → a ∼ a' 
               → (¬ a) ∼ (¬ a')
  ∼-respects-¬ a a' x = 
               ¬-I (¬-E (exchange (weakening (proj₂ x))) 
                        (weakening (axiom Z))) ,
               ¬-I (¬-E (exchange (weakening (proj₁ x))) 
                        (weakening (axiom Z)))
\end{code}
%</eq-respects-neg>

\begin{code}
  -------------------------------------------------------------------
  -- Definition: Binary operations and propositional constants in LT
  -------------------------------------------------------------------
\end{code}

%<*LT-conj>
\begin{code}
  _∧/_ : LindenbaumTarski → LindenbaumTarski → LindenbaumTarski
  A ∧/ B = setQuotBinOp ∼-refl ∼-refl _∧_ ∼-respects-∧ A B
\end{code}
%</LT-conj>

%<*LT-disj>
\begin{code}
  _∨/_ : LindenbaumTarski  → LindenbaumTarski → LindenbaumTarski
  A ∨/ B = setQuotBinOp ∼-refl ∼-refl _∨_ ∼-respects-∨ A B
\end{code}
%</LT-disj>

%<*LT-neg>
\begin{code}
  ¬/_ : LindenbaumTarski → LindenbaumTarski
  ¬/ A = setQuotUnaryOp ¬_ ∼-respects-¬ A
\end{code}
%</LT-neg>

%<*LT-top>
\begin{code}
  ⊤/ : LindenbaumTarski
  ⊤/ = [ ⊤ ]
\end{code}
%</LT-top>

%<*LT-bot>
\begin{code}
  ⊥/ : LindenbaumTarski
  ⊥/ = [ ⊥ ]
\end{code}
%</LT-bot>

\begin{code}
  ------------------------------------------------------------
  -- If ϕ is provable in Γ then [ϕ] should be the same as ⊤/.
  -- We can view this as a form of soundness.
  ------------------------------------------------------------
\end{code}

%<*sound>
\begin{code}
  sound : ∀ {ϕ : Formula} → Γ ⊢ ϕ → [ ϕ ] ≡ ⊤/
  sound x = eq/ _ _ (⊤-I , weakening x)
\end{code}
%</sound>

\begin{code}
  -------------------------------------------------------------
  -- By proving the Lindenbaum-Tarski algebra can be viewed as
  -- a complemented distributive lattice, we prove that it is
  -- also boolean.
  -------------------------------------------------------------
\end{code}

%<*LT-DistLattice>
\begin{code}
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
        ∧/-abs = elimProp2 (λ _ _ → squash/ _ _) 
                            λ _ _ → eq/ _ _ (∧-E₁ (axiom Z) , 
                                             ∧-I (axiom Z) (∨-I₂ (axiom Z)))

        ∨/-abs : ∀ (A B : LindenbaumTarski) → (A ∧/ B) ∨/ B ≡ B
        ∨/-abs = elimProp2 (λ _ _ → squash/ _ _) 
                            λ _ _ → eq/ _ _ (∨-E (axiom Z) (∧-E₂ (axiom Z)) (axiom Z) , 
                                             ∨-I₁ (axiom Z))

        ∨/-id : ∀ (A : LindenbaumTarski) → A ∨/ ⊥/ ≡ A
        ∨/-id = elimProp (λ _ → squash/ _ _) 
                          λ _ → eq/ _ _ (∨-E (axiom Z) (axiom Z) (⊥-E (axiom Z)) , 
                                         ∨-I₂ (axiom Z))

        ∧/-id : ∀ (A : LindenbaumTarski) → A ∧/ ⊤/ ≡ A
        ∧/-id = elimProp (λ _ → squash/ _ _) 
                          λ _ → eq/ _ _ (∧-E₁ (axiom Z) , 
                                         ∧-I (axiom Z) ⊤-I)
\end{code}
%</LT-DistLattice>
%<*LT-complemented>
\begin{code}
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
        ∧/-comp = elimProp (λ _ → squash/ _ _) 
                          λ _ → eq/ _ _ (¬-E (∧-E₁ (axiom Z)) (∧-E₂ (axiom Z)) , 
                                          ⊥-E (axiom Z))
\end{code}
%</LT-complemented>
%</src>