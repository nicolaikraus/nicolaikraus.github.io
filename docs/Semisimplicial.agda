-- An approach to defining semi-simplicial types.
-- This files comes together with a Haskell file (generateSemiSimp.hs) which can be used to generate the definitions of semi-simplicial types.
-- However, there are at least 2 caveats:

-- 1. The Agda definitions that are generated are not literally the "intuitive" ones, but they are equivalent to those that one would probably expect.
-- 2. My approach of generating these definitions is very ad-hoc and ugly (there would be much better ways to do it, see generateSemiSimp.hs). This also results in unreadability of the generated Agda code. This is therefore mainly a "proof of concept" (I wanted to convince myself that the definition I had in mind really type checks for all cases with "fixed n", even though it does not type check for general n).

module Semisimplicial where

Type = Set 

data Empty : Type where

data ⊤ : Type where
  * : ⊤

data ℕ : Type where
  O : ℕ
  S : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO O #-}
{-# BUILTIN SUC S #-}


data Fin : ℕ → Type where
  fz : {n : ℕ} → Fin (S n)
  fs : {n : ℕ} → Fin n → Fin (S n)

_>fin_ : {n : ℕ} → (i j : Fin n) → Set
fz >fin i = Empty
fs j >fin fz = ⊤
fs j >fin fs i = j >fin i

is-increasing : {m n : ℕ} → (Fin m → Fin n) → Type
is-increasing {m} {n} f = {j i : Fin m} → (j >fin i) → ((f j) >fin (f i))


infixr 1 _,_

record Σ (A : Type) (B : A → Type) : Type where
  constructor _,_
  field
    fst : A
    snd : B fst


_⇒+_ : ℕ → ℕ → Set
m ⇒+ n = Σ (Fin m → Fin n) is-increasing

_∘+_ : {l m n : ℕ} → (m ⇒+ n) → (l ⇒+ m) → (l ⇒+ n)
(g , p₂) ∘+ (f , p₁) = (λ i → g(f(i))) , (λ p → p₂ (p₁ p))


{- 
Assume we have already defined the types X₀ , X₁ , ... , Xₙ₋₁. 
These are the types of "standard" semi-simplicial complexes for the first n levels.
It will follow from the inductive definition what their types are; intuitively, they should be like this:

X₀ : Type
X₁ : X₀ → X₀ → Type
X₂ : (a b c : X₀) → (X₁ a b) → (X₁ b c) → (X₁ a c) → Type
...
Xₙ₋₁ : ...

but in fact, the types will only be equivalent (but not strictly equal) to those expressions.

What we would like to say is this:

Let P_n (the n-boundary) be the type of tuples

 (x₁ , x₂ , ... , xₙ₋₁),

 where x_k is of type

    (fk : (S k) ⇒+ (S n)) 
  → X_k ( [ λ (gj : (S j) ⇒+ (S k)) . x_j(fk ∘+ gj)]_{j : Fin k} )

(we write [a_j]_{j : Fin k} for the tupel (a_1 , a_2 , ... , a_{k-1})).

We define Xₙ to be

Xₙ : P_n → Type.

Unfortunately, Agda can not see that this type-checks.

The Haskell file generateSemiSimpl.hs generates the definitions of X₀ , X₁ , ... , Xₙ. They may be copied below to type check them. Here is the output for n ≡ 7:
[note that we want to give the type of "standard" semi-simplicial types, not an actual semi-simplicial type; that is why the definitions of X₀ , X₁ , ... are missing.]
-}


P0 = ⊤

X0 : P0 → Type
X0 = {!!}


P1 = Σ ((f0 : (S 0) ⇒+ (S 1)) → X0 (*))  λ x0 → ⊤ 

X1 : P1 → Type
X1 = {!!}


P2 = Σ ((f0 : (S 0) ⇒+ (S 2)) → X0 (*))  λ x0 → Σ ((f1 : (S 1) ⇒+ (S 2)) → X1 ((λ (g0 : (S 0) ⇒+ (S 1)) → x0(f1 ∘+ g0)) , *))  λ x1 → ⊤  

X2 : P2 → Type
X2 = {!!}


P3 = Σ ((f0 : (S 0) ⇒+ (S 3)) → X0 (*))  λ x0 → Σ ((f1 : (S 1) ⇒+ (S 3)) → X1 ((λ (g0 : (S 0) ⇒+ (S 1)) → x0(f1 ∘+ g0)) , *))  λ x1 → Σ ((f2 : (S 2) ⇒+ (S 3)) → X2 ((λ (g0 : (S 0) ⇒+ (S 2)) → x0(f2 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 2)) → x1(f2 ∘+ g1)) , *))  λ x2 → ⊤   

X3 : P3 → Type
X3 = {!!}


P4 = Σ ((f0 : (S 0) ⇒+ (S 4)) → X0 (*))  λ x0 → Σ ((f1 : (S 1) ⇒+ (S 4)) → X1 ((λ (g0 : (S 0) ⇒+ (S 1)) → x0(f1 ∘+ g0)) , *))  λ x1 → Σ ((f2 : (S 2) ⇒+ (S 4)) → X2 ((λ (g0 : (S 0) ⇒+ (S 2)) → x0(f2 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 2)) → x1(f2 ∘+ g1)) , *))  λ x2 → Σ ((f3 : (S 3) ⇒+ (S 4)) → X3 ((λ (g0 : (S 0) ⇒+ (S 3)) → x0(f3 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 3)) → x1(f3 ∘+ g1)) , (λ (g2 : (S 2) ⇒+ (S 3)) → x2(f3 ∘+ g2)) , *))  λ x3 → ⊤    

X4 : P4 → Type
X4 = {!!}


P5 = Σ ((f0 : (S 0) ⇒+ (S 5)) → X0 (*))  λ x0 → Σ ((f1 : (S 1) ⇒+ (S 5)) → X1 ((λ (g0 : (S 0) ⇒+ (S 1)) → x0(f1 ∘+ g0)) , *))  λ x1 → Σ ((f2 : (S 2) ⇒+ (S 5)) → X2 ((λ (g0 : (S 0) ⇒+ (S 2)) → x0(f2 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 2)) → x1(f2 ∘+ g1)) , *))  λ x2 → Σ ((f3 : (S 3) ⇒+ (S 5)) → X3 ((λ (g0 : (S 0) ⇒+ (S 3)) → x0(f3 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 3)) → x1(f3 ∘+ g1)) , (λ (g2 : (S 2) ⇒+ (S 3)) → x2(f3 ∘+ g2)) , *))  λ x3 → Σ ((f4 : (S 4) ⇒+ (S 5)) → X4 ((λ (g0 : (S 0) ⇒+ (S 4)) → x0(f4 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 4)) → x1(f4 ∘+ g1)) , (λ (g2 : (S 2) ⇒+ (S 4)) → x2(f4 ∘+ g2)) , (λ (g3 : (S 3) ⇒+ (S 4)) → x3(f4 ∘+ g3)) , *))  λ x4 → ⊤     

X5 : P5 → Type
X5 = {!!}


P6 = Σ ((f0 : (S 0) ⇒+ (S 6)) → X0 (*))  λ x0 → Σ ((f1 : (S 1) ⇒+ (S 6)) → X1 ((λ (g0 : (S 0) ⇒+ (S 1)) → x0(f1 ∘+ g0)) , *))  λ x1 → Σ ((f2 : (S 2) ⇒+ (S 6)) → X2 ((λ (g0 : (S 0) ⇒+ (S 2)) → x0(f2 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 2)) → x1(f2 ∘+ g1)) , *))  λ x2 → Σ ((f3 : (S 3) ⇒+ (S 6)) → X3 ((λ (g0 : (S 0) ⇒+ (S 3)) → x0(f3 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 3)) → x1(f3 ∘+ g1)) , (λ (g2 : (S 2) ⇒+ (S 3)) → x2(f3 ∘+ g2)) , *))  λ x3 → Σ ((f4 : (S 4) ⇒+ (S 6)) → X4 ((λ (g0 : (S 0) ⇒+ (S 4)) → x0(f4 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 4)) → x1(f4 ∘+ g1)) , (λ (g2 : (S 2) ⇒+ (S 4)) → x2(f4 ∘+ g2)) , (λ (g3 : (S 3) ⇒+ (S 4)) → x3(f4 ∘+ g3)) , *))  λ x4 → Σ ((f5 : (S 5) ⇒+ (S 6)) → X5 ((λ (g0 : (S 0) ⇒+ (S 5)) → x0(f5 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 5)) → x1(f5 ∘+ g1)) , (λ (g2 : (S 2) ⇒+ (S 5)) → x2(f5 ∘+ g2)) , (λ (g3 : (S 3) ⇒+ (S 5)) → x3(f5 ∘+ g3)) , (λ (g4 : (S 4) ⇒+ (S 5)) → x4(f5 ∘+ g4)) , *))  λ x5 → ⊤      

X6 : P6 → Type
X6 = {!!}


P7 = Σ ((f0 : (S 0) ⇒+ (S 7)) → X0 (*))  λ x0 → Σ ((f1 : (S 1) ⇒+ (S 7)) → X1 ((λ (g0 : (S 0) ⇒+ (S 1)) → x0(f1 ∘+ g0)) , *))  λ x1 → Σ ((f2 : (S 2) ⇒+ (S 7)) → X2 ((λ (g0 : (S 0) ⇒+ (S 2)) → x0(f2 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 2)) → x1(f2 ∘+ g1)) , *))  λ x2 → Σ ((f3 : (S 3) ⇒+ (S 7)) → X3 ((λ (g0 : (S 0) ⇒+ (S 3)) → x0(f3 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 3)) → x1(f3 ∘+ g1)) , (λ (g2 : (S 2) ⇒+ (S 3)) → x2(f3 ∘+ g2)) , *))  λ x3 → Σ ((f4 : (S 4) ⇒+ (S 7)) → X4 ((λ (g0 : (S 0) ⇒+ (S 4)) → x0(f4 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 4)) → x1(f4 ∘+ g1)) , (λ (g2 : (S 2) ⇒+ (S 4)) → x2(f4 ∘+ g2)) , (λ (g3 : (S 3) ⇒+ (S 4)) → x3(f4 ∘+ g3)) , *))  λ x4 → Σ ((f5 : (S 5) ⇒+ (S 7)) → X5 ((λ (g0 : (S 0) ⇒+ (S 5)) → x0(f5 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 5)) → x1(f5 ∘+ g1)) , (λ (g2 : (S 2) ⇒+ (S 5)) → x2(f5 ∘+ g2)) , (λ (g3 : (S 3) ⇒+ (S 5)) → x3(f5 ∘+ g3)) , (λ (g4 : (S 4) ⇒+ (S 5)) → x4(f5 ∘+ g4)) , *))  λ x5 → Σ ((f6 : (S 6) ⇒+ (S 7)) → X6 ((λ (g0 : (S 0) ⇒+ (S 6)) → x0(f6 ∘+ g0)) , (λ (g1 : (S 1) ⇒+ (S 6)) → x1(f6 ∘+ g1)) , (λ (g2 : (S 2) ⇒+ (S 6)) → x2(f6 ∘+ g2)) , (λ (g3 : (S 3) ⇒+ (S 6)) → x3(f6 ∘+ g3)) , (λ (g4 : (S 4) ⇒+ (S 6)) → x4(f6 ∘+ g4)) , (λ (g5 : (S 5) ⇒+ (S 6)) → x5(f6 ∘+ g5)) , *))  λ x6 → ⊤       

X7 : P7 → Type
X7 = {!!}

