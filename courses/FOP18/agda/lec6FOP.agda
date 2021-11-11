{- 
  Mathematical Foundations of Programming (G54FOP)
  Nicolai Kraus
  Lecture 6, 15 Feb 2018
-}

module lec6FOP where

{- We import everything we have done last week.
   "open" means we can use all definitions directly -}
open import lec3FOP

{- Hint: middle mouse click or alt-.
   [press alt/meta, then .]
   jumps to the definition that the cursor is on -}

-- Reduce in one step
-- (these are the simplification rules)
data _→1_ : Expr → Expr → Set where
  izz : iz z →1 t
  izs : {e : Expr} → iz (s e) →1 f
  ift : {e₂ e₃ : Expr} → (if t then e₂ else e₃) →1 e₂
  iff : {e₂ e₃ : Expr} → (if f then e₂ else e₃) →1 e₃
  ps  : {e : Expr} → p (s e) →1 e
  pz  : p z →1 z

-- include structural rules
data _↝_ : Expr → Expr → Set where  -- type: \leadsto
  from→1   : {e₁ e₂ : Expr} → (e₁ →1 e₂) → (e₁ ↝ e₂)
  inside-s : {e₁ e₂ : Expr} → (e₁ ↝ e₂) → (s e₁ ↝ s e₂)
  inside-p : {e₁ e₂ : Expr} → (e₁ ↝ e₂) → (p e₁ ↝ p e₂)
  inside-iz : ∀ {e₁} {e₂} → (e₁ ↝ e₂) → (iz e₁ ↝ iz e₂)
  inside-ite1 : ∀ {e₁ e₁' e₂ e₃} → (e₁ ↝ e₁')
    → (if e₁ then e₂ else e₃) ↝ (if e₁' then e₂ else e₃)
  inside-ite2 : ∀ {e₁ e₂ e₂' e₃} → (e₂ ↝ e₂')
    → (if e₁ then e₂ else e₃) ↝ (if e₁ then e₂' else e₃)
  inside-ite3 : ∀ {e₁ e₂ e₃ e₃'} → (e₃ ↝ e₃')
    → (if e₁ then e₂ else e₃) ↝ (if e₁ then e₂ else e₃')

data _↝*_ : Expr → Expr → Set where
  start : ∀ {e} → e ↝* e
  step  : ∀ {e₁ e₂ e₃} → (e₁ ↝ e₂) → (e₂ ↝* e₃)
          → (e₁ ↝* e₃)

-- compose two reduction sequences
compose : {e₁ e₂ e₃ : Expr} → (e₁ ↝* e₂)
          → (e₂ ↝* e₃)
          → (e₁ ↝* e₃)
compose start s₂ = s₂
compose (step x s₁) s₂ = step x (compose s₁ s₂)

open import Data.Empty renaming (⊥ to ∅)  -- \emptyset

-- define what it means to be a normal form
is-normal : Expr → Set
is-normal e = (e₁ : Expr) → (e →1 e₁) → ∅

{- Exercises:
   1. (easy) Show that the expression "t" is
      in normal form. This means: fill the whole
      (replace the question mark) in
        t-nf : is-normal t
        t-nf = ?

   2. (medium) Show that, if "e" is a normal form,
      then so is "s e".

   3. (hard) Show that "is-normal" is a
      decidable predicate on Expr. 
      This means writing a function
      which takes an expression and tells us
      whether the expression is a normal form
      or not. The naive version would be
         Expr → Bool
      but we can do much better: we can take an
      expression "e" and either return a *proof*
      that "e" is a normal form, or return an
      example of how it can be reduced.
      Such an example would consist of an expression
      "reduct" and a proof of "e ↝ reduct"; we
      will learn later how this can be expressed,
      but a good way of implementing it is as follows:
-}

record can-red (e : Expr) : Set where
  field
    reduct  : Expr
    redstep : e ↝ reduct

{- Ex 3, continued: We can import Data.Sum to get the
   definition of ⊎ (type: \u+), a disjoint sum (it's
   Either in Haskell). Check out how ⊎ is defined in
   the library, it's really simple! -}

open import Data.Sum

{- Ex3, continued: Now, fill in the ? in the following
   function; probably, you will want more auxiliary
   lemma. Caveat: I have not done this myself. 
   
decide-nf : (e : Expr) → (is-normal e) ⊎ can-red e
decide-nf e = {!!}

-}
