%<*all>
\begin{code}
{-# OPTIONS --cubical #-}
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

\begin{code}
infix  35  _∧_
infix  30  _∨_
infixl 36  ¬_
infix  20  _⊢_
infix  23  _∶_
\end{code}

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
-- {-# NO_POSITIVITY_CHECK #-}
\end{code}

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

\begin{code}
--  ∨-E : {Γ : ctxt} {ϕ ψ γ : Formula}
--      → Γ ⊢ ϕ ∨ ψ
--      → (Γ ⊢ ϕ → Γ ⊢ γ)
--      → (Γ ⊢ ψ → Γ ⊢ γ)
--      → Γ ⊢ γ
\end{code}

%<*negI>
\begin{code}
  ¬-I : {Γ : ctxt} {ϕ : Formula}
      → Γ ∶ ϕ ⊢ ⊥
      → Γ ⊢ ¬ ϕ
\end{code}
%</negI>

\begin{code}
--  ¬-I : {Γ : ctxt} {ϕ : Formula}
--      → (Γ ⊢ ϕ → Γ ⊢ ⊥)
--      → Γ ⊢ ¬ ϕ
\end{code}

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
  ⊤-I : {Γ : ctxt} 
      → Γ ⊢ ⊤
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
--  contraction : {Γ : ctxt} {ϕ ψ : Formula} → ((Γ ∶ ϕ) ∶ ϕ) ⊢ ψ → (Γ ∶ ϕ) ⊢ ψ
\end{code}

\begin{code}
module _ {Γ : ctxt} where

  infixl 25 ¬/_

  ----------------------------------------
  -- Properties of propositional calculus
  ----------------------------------------

  -- Commutativity on ∧
\end{code}

%<*conj-comm>
\begin{code}
  ∧-comm : ∀ {ϕ ψ : Formula} → Γ ∶ ϕ ∧ ψ ⊢ ψ ∧ ϕ
  ∧-comm = ∧-I (∧-E₂ (axiom Z)) (∧-E₁ (axiom Z))
\end{code}
%</conj-comm>

\begin{code}
--  ∧-comm : ∀ {ϕ ψ : Formula} → Γ ⊢ ϕ ∧ ψ → Γ ⊢ ψ ∧ ϕ
--  ∧-comm x = ∧-I (∧-E₂ x) (∧-E₁ x)
\end{code}

\begin{code}
  -- Commutativity on ∨
\end{code}

%<*disj-comm>
\begin{code}
  ∨-comm : {ϕ ψ : Formula} → Γ ∶ ϕ ∨ ψ ⊢ ψ ∨ ϕ
  ∨-comm = ∨-E (axiom Z) (∨-I₁ (axiom Z)) (∨-I₂ (axiom Z))
\end{code}
%</disj-comm>

\begin{code}
--  ∨-comm : {ϕ ψ : Formula} → Γ ⊢ ϕ ∨ ψ → Γ ⊢ ψ ∨ ϕ
--  ∨-comm x = ∨-E x ∨-I₁ ∨-I₂
\end{code}

\begin{code}
  -- Associativity on ∧
\end{code}

%<*conj-ass1>
\begin{code}
  ∧-assoc1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∧ (ψ ∧ γ) ⊢ (ϕ ∧ ψ) ∧ γ
  ∧-assoc1 = ∧-I (∧-I (∧-E₁ (axiom Z))
                      (∧-E₁ (∧-E₂ (axiom Z))))
                 (∧-E₂ (∧-E₂ (axiom Z)))
\end{code}
%</conj-ass1>

\begin{code}
--  ∧-assoc1 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∧ (ψ ∧ γ) → Γ ⊢ (ϕ ∧ ψ) ∧ γ
--  ∧-assoc1 x = ∧-I (∧-I (∧-E₁ x) (∧-E₁ (∧-E₂ x)))
--                       (∧-E₂ (∧-E₂ x))
\end{code}

%<*conj-ass2>
\begin{code}             
  ∧-assoc2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∧ ψ) ∧ γ ⊢ ϕ ∧ (ψ ∧ γ)
  ∧-assoc2 = ∧-I (∧-E₁ (∧-E₁ (axiom Z)))
                 (∧-I (∧-E₂ (∧-E₁ (axiom Z)))
                      (∧-E₂ (axiom Z)))
\end{code}
%</conj-ass2>

\begin{code}
--  ∧-assoc2 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ∧ ψ) ∧ γ → Γ ⊢ ϕ ∧ (ψ ∧ γ)
--  ∧-assoc2 x = ∧-I (∧-E₁ (∧-E₁ x))
--                       (∧-I (∧-E₂ (∧-E₁ x)) (∧-E₂ x))
\end{code}

\begin{code}
  -- Associativity on ∨
\end{code}

%<*disj-ass1>
\begin{code}
  ∨-assoc1 : ∀ {ϕ ψ γ : Formula} → Γ ∶ ϕ ∨ (ψ ∨ γ) ⊢ (ϕ ∨ ψ) ∨ γ
  ∨-assoc1 = ∨-E (axiom Z)
                 (∨-I₂ (∨-I₂ (axiom Z)))
                 (∨-E (axiom Z)
                      (∨-I₂ (∨-I₁ (axiom Z)))
                      (∨-I₁ (axiom Z)))
\end{code}
%</disj-ass1>

\begin{code}
--  ∨-assoc1 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∨ (ψ ∨ γ) → Γ ⊢ (ϕ ∨ ψ) ∨ γ
--  ∨-assoc1 x = ∨-E x (λ y → ∨-I₂ (∨-I₂ y))
--                         λ y → ∨-E y (λ z → ∨-I₂ (∨-I₁ z)) ∨-I₁
\end{code}

%<*disj-ass2>
\begin{code}
  ∨-assoc2 : ∀ {ϕ ψ γ : Formula} → Γ ∶ (ϕ ∨ ψ) ∨ γ ⊢ ϕ ∨ (ψ ∨ γ)
  ∨-assoc2 = ∨-E (axiom Z)
                 (∨-E (axiom Z)
                      (∨-I₂ (axiom Z))
                      (∨-I₁ (∨-I₂ (axiom Z))))
                 (∨-I₁ (∨-I₁ (axiom Z)))
\end{code}
%</disj-ass2>

\begin{code}
--  ∨-assoc2 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ∨ ψ) ∨ γ → Γ ⊢ ϕ ∨ (ψ ∨ γ)
--  ∨-assoc2 x = ∨-E x (λ y → ∨-E y ∨-I₂ λ z → ∨-I₁ (∨-I₂ z)) λ y → ∨-I₁ (∨-I₁ y)
\end{code}

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

\begin{code}
--  ∧-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∧ (ψ ∨ γ) → Γ ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
--  ∧-dist1 x = ∨-E (∧-E₂ x) (λ y → ∨-I₂ (∧-I (∧-E₁ x) y))
--                              λ y → ∨-I₁ (∧-I (∧-E₁ x) y)
\end{code}

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

\begin{code}
--  ∧-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ) → Γ ⊢ ϕ ∧ (ψ ∨ γ)
--  ∧-dist2 x = ∧-I (∨-E x ∧-E₁ ∧-E₁)
--                      (∨-E x (λ y → ∨-I₂ (∧-E₂ y))
--                              λ y → ∨-I₁ (∧-E₂ y))
\end{code}

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

\begin{code}
--  ∨-dist1 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ∨ (ψ ∧ γ) → Γ ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
--  ∨-dist1 x = ∨-E x (λ y → ∧-I (∨-I₂ y) (∨-I₂ y))
--                     λ y → ∧-I (∨-I₁ (∧-E₁ y)) (∨-I₁ (∧-E₂ y))
\end{code}

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

\begin{code}
--  ∨-dist2 : ∀ {ϕ ψ γ : Formula} → Γ ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ) → Γ ⊢ ϕ ∨ (ψ ∧ γ)
--  ∨-dist2 x = ∨-E (∧-E₁ x) ∨-I₂ λ y → ∨-E (∧-E₂ x) ∨-I₂  λ z → ∨-I₁ (∧-I y z)
\end{code}

\begin{code}
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

\begin{code}
--  _∼_ : Formula → Formula → Type
--  ϕ ∼ ψ = (Γ ⊢ ϕ → Γ ⊢ ψ) × (Γ ⊢ ψ → Γ ⊢ ϕ)
\end{code}

%<*refl>
\begin{code}
  ∼-refl : ∀ (ϕ : Formula) → ϕ ∼ ϕ
  ∼-refl _ = axiom Z , (axiom Z)
\end{code}
%</refl>

\begin{code}
--  ∼-refl : ∀ (ϕ : Formula) → ϕ ∼ ϕ
--  ∼-refl _ = (λ x → x) , (λ x → x)
\end{code}

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

\begin{code}
--  ⊢trans : ∀ {ϕ ψ γ : Formula} → (Γ ⊢ ϕ → Γ ⊢ ψ) → (Γ ⊢ ψ → Γ ⊢ γ) → (Γ ⊢ ϕ → Γ ⊢ γ)
--  ⊢trans x y z = y (x z)
\end{code}

%<*trans>
\begin{code}
  ∼-trans : ∀ {ϕ ψ γ : Formula} → ϕ ∼ γ → γ ∼ ψ → ϕ ∼ ψ
  ∼-trans x y = ⊢trans (proj₁ x) (proj₁ y) , ⊢trans (proj₂ y) (proj₂ x)
\end{code}
%</trans>

%<*comm-eq-conj>
\begin{code}
  comm-eq-∧ : ∀ {ϕ ψ : Formula} → ϕ ∧ ψ ∼ ψ ∧ ϕ
  comm-eq-∧ = ∧-comm , ∧-comm
\end{code}
%</comm-eq-conj>

%<*comm-eq-disj>
\begin{code}
  comm-eq-∨ : ∀ {ϕ ψ : Formula} → ϕ ∨ ψ ∼ ψ ∨ ϕ
  comm-eq-∨ = ∨-comm , ∨-comm
\end{code}
%</comm-eq-disj>

%<*ass-eq-conj>
\begin{code}
  ass-eq-∧ : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∧ γ) ∼ (ϕ ∧ ψ) ∧ γ
  ass-eq-∧ = ∧-assoc1 , ∧-assoc2
\end{code}
%</ass-eq-conj>

%<*ass-eq-disj>
\begin{code}
  ass-eq-∨ : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∨ γ) ∼ (ϕ ∨ ψ) ∨ γ
  ass-eq-∨ = ∨-assoc1 , ∨-assoc2
\end{code}
%</ass-eq-disj>

%<*dist-eq-conj>
\begin{code}
  dist-eq-∧ : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∨ γ) ∼ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  dist-eq-∧ = ∧-dist1 , ∧-dist2
\end{code}
%</dist-eq-conj>

%<*dist-eq-disj>
\begin{code}
  dist-eq-∨ : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∧ γ) ∼ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  dist-eq-∨ = ∨-dist1 , ∨-dist2
\end{code}
%</dist-eq-disj>

\begin{code}
  ---------------------------------------------------------
  -- Lindenbaum-Tarski algebra is defined as the quotioent
  -- algebra obtained by factoring the algebra of formulas
  -- by the defined equivalence relation.
  ---------------------------------------------------------
\end{code}

%<*LT-def>
\begin{code}
  LindenbaumTarski : Type
  LindenbaumTarski = Formula / _∼_
\end{code}
%</LT-def>

\begin{code}
  --------------------------------------------------
  -- The equivalence relation ∼ respects operations
  --------------------------------------------------
\end{code}

%<*eq-respects-conj>
\begin{code}
  ∼-respects-∧ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∧ b) ∼ (a' ∧ b')
  ∼-respects-∧ a a' b b' x y = ∧-I (⊢trans (∧-E₁ (axiom Z)) (proj₁ x))
                                   (⊢trans (∧-E₂ (axiom Z)) (proj₁ y)) ,
                               ∧-I (⊢trans (∧-E₁ (axiom Z)) (proj₂ x))
                                   (⊢trans (∧-E₂ (axiom Z)) (proj₂ y))
\end{code}
%</eq-respects-conj>

\begin{code}
--  ∼-respects-∧ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∧ b) ∼ (a' ∧ b')
--  ∼-respects-∧ a a' b b' x y = (λ z → ∧-I (proj₁ x (∧-E₁ z)) (proj₁ y (∧-E₂ z))) ,
--                               (λ z → ∧-I (proj₂ x (∧-E₁ z)) (proj₂ y (∧-E₂ z)))
\end{code}

%<*eq-respects-disj>
\begin{code}
  ∼-respects-∨ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∨ b) ∼ (a' ∨ b')
  ∼-respects-∨ a a' b b' x y = ∨-E (axiom Z)
                                   (exchange (weakening (∨-I₂ (proj₁ x))))
                                   (exchange (weakening (∨-I₁ (proj₁ y)))) ,
                               ∨-E (axiom Z)
                                   (exchange (weakening (∨-I₂ (proj₂ x))))
                                   (exchange (weakening (∨-I₁ (proj₂ y))))
\end{code}
%</eq-respects-disj>

\begin{code}
--  ∼-respects-∨ : ∀ (a a' b b' : Formula) → a ∼ a' → b ∼ b' → (a ∨ b) ∼ (a' ∨ b')
--  ∼-respects-∨ a a' b b' A B = (λ x → ∨-E x (λ x → ∨-I₂ (proj₁ A x)) λ x → ∨-I₁ (proj₁ B x)) , λ x → ∨-E x (λ x → ∨-I₂ (proj₂ A x)) λ x → ∨-I₁ (proj₂ B x)
\end{code}

%<*eq-respects-neg>
\begin{code}
  ∼-respects-¬ : ∀ (a a' : Formula) → a ∼ a' → (¬ a) ∼ (¬ a')
  ∼-respects-¬ a a' x = ¬-I (¬-E (exchange (weakening (proj₂ x))) (weakening (axiom Z))) ,
                        ¬-I (¬-E (exchange (weakening (proj₁ x))) (weakening (axiom Z)))
\end{code}
%</eq-respects-neg>

\begin{code}
--  ∼-respects-¬ : ∀ (a a' : Formula) → a ∼ a' → (¬ a) ∼ (¬ a')
--  ∼-respects-¬ a a' A = (λ x → ¬-I (λ y → ¬-E (proj₂ A y) x)), (λ x → ¬-I (λ y → ¬-E (proj₁ A y) x))
\end{code}

\begin{code}
  -------------------------------------------------------------------
  -- Definition: Binary operations and propositional constants in LT
  -------------------------------------------------------------------
\end{code}

%<*LT-conj>
\begin{code}
  _⋀_ : LindenbaumTarski → LindenbaumTarski → LindenbaumTarski
  A ⋀ B = setQuotBinOp ∼-refl ∼-refl _∧_ ∼-respects-∧ A B
\end{code}
%</LT-conj>

%<*LT-disj>
\begin{code}
  _⋁_ : LindenbaumTarski  → LindenbaumTarski → LindenbaumTarski
  A ⋁ B = setQuotBinOp ∼-refl ∼-refl _∨_ ∼-respects-∨ A B
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
 

  -- Commutativity on LT 
  %<*LT-comm>
  \begin{code}
  ⋀-comm : ∀ (A B : LindenbaumTarski) → A ⋀ B ≡ B ⋀ A
  ⋀-comm = elimProp2 (λ _ _ → squash/ _ _) λ ϕ ψ → eq/ _ _ (∼-sym (∧-comm , ∧-comm))

  ⋁-comm : ∀ (A B : LindenbaumTarski) → A ⋁ B ≡ B ⋁ A
  ⋁-comm = elimProp2 (λ _ _ → squash/ _ _) λ ϕ ψ → eq/ _ _ (∼-sym (∨-comm , ∨-comm))
  \end{code}
  %</LT-comm>

  -- Associativity on LT
  %<*LT-ass>
  \begin{code}
  ⋀-assoc : ∀ (A B C : LindenbaumTarski) → A ⋀ (B ⋀ C) ≡ (A ⋀ B) ⋀ C
  ⋀-assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∧-assoc1 , ∧-assoc2)

  ⋁-assoc : ∀ (A B C : LindenbaumTarski) → A ⋁ (B ⋁ C) ≡ (A ⋁ B) ⋁ C
  ⋁-assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∨-assoc1 , ∨-assoc2)
\end{code}
%</LT-ass>

  -- Distributivity over LT
  %<*LT-dist>
  \begin{code}
  ⋀-dist : ∀ (A B C : LindenbaumTarski) → A ⋀ (B ⋁ C) ≡ (A ⋀ B) ⋁ (A ⋀ C)
  ⋀-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∧-dist1 , ∧-dist2)

  ⋁-dist : ∀ (A B C : LindenbaumTarski) → A ⋁ (B ⋀ C) ≡ (A ⋁ B) ⋀ (A ⋁ C)
  ⋁-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ (∨-dist1 , ∨-dist2)
  \end{code}
  %</LT-dist>

\begin{code}
  -- Definition: Superweakening
  superweakening : ∀ (Γ : ctxt) → Γ ⊢ ⊤
  superweakening ∅ = ⊤-I
  superweakening (Δ ∶ x) = weakening (superweakening Δ)
\end{code}

\begin{code}
  -- Absorbtion law ⋁
  ⋁-abs : ∀ (A B : LindenbaumTarski) → (A ⋀ B) ⋁ B ≡ B
  ⋁-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∨-E (axiom Z) (∧-E₂ (axiom Z)) (axiom Z) , ∨-I₁ (axiom Z))
--  ⋁-abs : ∀ (A B : LindenbaumTarski) → (A ⋀ B) ⋁ B ≡ B
--  ⋁-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ((λ x → ∨-E x ∧-E₂ λ a → a) , ∨-I₁) 

  -- Absorbtion law ⋀
  ⋀-abs : ∀ (A B : LindenbaumTarski) → A ⋀ (A ⋁ B) ≡ A
  ⋀-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∧-E₁ (axiom Z) , ∧-I (axiom Z) (∨-I₂ (axiom Z)))
--  ⋀-abs : ∀ (A B : LindenbaumTarski) → A ⋀ (A ⋁ B) ≡ A
--  ⋀-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ (∧-E₁ , λ x → ∧-I x (∨-I₂ x))

  -- Identity law ⋁
  ⋁-id : ∀ (A : LindenbaumTarski) → A ⋁ ⊥/ ≡ A
  ⋁-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∨-E (axiom Z) (axiom Z) (⊥-E (axiom Z)) , ∨-I₂ (axiom Z))
--  ⋁-id : ∀ (A : LindenbaumTarski) → A ⋁ ⊥/ ≡ A
--  ⋁-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ((λ x → ∨-E x (λ y → y) ⊥-E) , ∨-I₂)

  -- Identity law ⋀
  ⋀-id : ∀ (A : LindenbaumTarski) → A ⋀ ⊤/ ≡ A
  ⋀-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∧-E₁ (axiom Z) , ∧-I (axiom Z) (superweakening _))
--  ⋀-id : ∀ (A : LindenbaumTarski) → A ⋀ ⊤/ ≡ A
--  ⋀-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (∧-E₁ , λ x → ∧-I x (superweakening _))


  ------------------------------------------------------------
  -- If ϕ is provable in Γ then [ϕ] should be the same as ⊤/.
  -- We can view this as a form of soundness.
  ------------------------------------------------------------
  sound : ∀ {ϕ : Formula} → Γ ⊢ ϕ → [ ϕ ] ≡ ⊤/
  sound x = eq/ _ _ (superweakening _ , weakening x)
--  sound : ∀ {ϕ : Formula} → Γ ⊢ ϕ → [ ϕ ] ≡ ⊤/
--  sound x = eq/ _ _ ((λ _ → superweakening _) , λ _ → x )


  -------------------------------------------------------------
  -- By proving the Lindenbaum-Tarski algebra can be viewed as
  -- a distributive lattice, we prove that it is also boolean.
  -------------------------------------------------------------
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


  -- Complemented
  ⋀-inv : ∀ (A : LindenbaumTarski) → A ⋀ ¬/ A ≡ ⊥/
  ⋀-inv = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (¬-E (∧-E₁ (axiom Z)) (∧-E₂ (axiom Z)) , ⊥-E (axiom Z))
--  ⋀-inv : ∀ (A : LindenbaumTarski) → A ⋀ ¬/ A ≡ ⊥/
--  ⋀-inv = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ((λ x → ¬-E (∧-E₁ x) (∧-E₂ x)) , λ x → ⊥-E x)
  
  ⋁-inv : ∀ (A : LindenbaumTarski) → A ⋁ ¬/ A ≡ ⊤/
  ⋁-inv = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ (superweakening _ , LEM)
--  ⋁-inv : ∀ (A : LindenbaumTarski) → A ⋁ ¬/ A ≡ ⊤/
--  ⋁-inv = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ((λ x → superweakening _) , λ x → LEM)
\end{code}
%</all>