\begin{code}
{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude

module examples where
\end{code}

%<*bool>
\begin{code}
data Bool : Type where
  true  : Bool
  false : Bool
\end{code}
%</bool>

%<*not>
\begin{code}
not : Bool → Bool
not true  = false
not false = true
\end{code}
%</not>

%<*nat>
\begin{code}
data ℕ : Type where
  zero : ℕ
  suc  : ℕ → ℕ
\end{code}
%</nat>

%<*add>
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)
\end{code}
%</add>

%<*infix>
\begin{code}
infix 25 _+_
\end{code}
%</infix>

%<*list>
\begin{code}
infix 20 _::_
data List (A : Type) : Type where
  [] : List A
  _::_ : A → List A → List A
\end{code}
%</list>

%<*id1>
\begin{code}
id : (A : Type) → A → A
id A x = x
\end{code}
%</id1>

%<*id2>
\begin{code}
id' : {A : Type} → A → A
id' x = x
\end{code}
%</id2>
