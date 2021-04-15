{-
    INTRODUCTION TO HOMOTOPY TYPE THEORY
        Midlands Graduate School 2021
              Nicolai Kraus

This is the Agda file which we looked at in the
exercise session(s).
-}

{-# OPTIONS --without-K #-}

open import Agda.Primitive

{-
Two inductive implementations of the
  Martin-Löf identity type
aka
  equality type
aka
  identification type
aka
  path type.
-}

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

infixr 10 _≡_

-- explcit
data _≡'_ {A : Set} : A → A → Set where
  refl : (a : A) → a ≡' a

-- variables can be used later and are understood as Pi-quantified.
variable
  A B C : Set

-- sym' for ≡'
sym' : {a b : A} → a ≡' b → b ≡' a
sym' {a = x} {.x} (refl .x) = refl x

-- sym for ≡
sym : {a b : A} → a ≡ b → b ≡ a
sym refl = refl

_⁻¹ = sym

symsym : {a b : A} → (p : a ≡ b) → sym (sym p) ≡ p
symsym refl = refl

ap : (f : A → B) → {a b : A} → a ≡ b → f a ≡ f b
ap f {a} {.a} refl = refl

_∘_ : {A B C : Set} → (g : B → C) → (f : A → B) → A → C
g ∘ f = λ x → g (f x)

infixl 26 _∘_

ap-g∘f : (f : A → B) (g : B → C) {a b : A} (p : a ≡ b)
         → ap (g ∘ f) p ≡ (ap g ∘ ap f) p
ap-g∘f f g refl = refl

trans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

_∙_ = trans
infixr 30 _∙_

sym-refl : {a b : A} → (p : a ≡ b) → (p ⁻¹) ∙ p ≡ refl
sym-refl refl = refl

trans2 : {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
trans2 p refl = p

trans-trans2 : {a b c : A} -> (p : a ≡ b) -> (q : b ≡ c)
               -> trans p q ≡ trans2 p q
trans-trans2 {a = x} {b = .x} {c = .x} refl refl = refl

trans3 : {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
trans3 refl refl = refl

trans-trans3 : {a b c : A} -> (p : a ≡ b) -> (q : b ≡ c)
               -> trans p q ≡ trans3 p q
trans-trans3 {a = x} {b = .x} {c = .x} refl refl = refl

test : {a c : A} → (q : a ≡ c) → trans refl q ≡ q
test q = refl

test2 : {a c : A} → (q : a ≡ c) → trans2 q refl ≡ q
test2 q = refl

test3 : {a c : A} → (q : a ≡ c) → trans3 refl q ≡ q
test3 refl = refl

{- In test3 above, we have to pattern match (path induct) on q!
   What if we cannot, as in

  test4 : {a : A} → (q : a ≡ a) → trans3 refl q ≡ q

  ?
-}

-- solution:
test4 : {a : A} → (q : a ≡ a) → trans3 refl q ≡ q
test4 q = test3 q

-- We can only pattern match on q if we remove the --without-K option:
uip : {a b : A} → (p q : a ≡ b) → p ≡ q
uip {a = x} {b = .x} refl q = {!q!}

-- implementation of the J eliminator (aka path induction)
module _ (C : (a b : A) → a ≡ b → Set) where

   J-elim : (d : (a : A) → C a a refl) → (a b : A) → (p : a ≡ b) → C a b p
   J-elim d a .a refl = d a

-- implementation of the Paulin-Mohring version of J (based bath induction)
module _ (a₀ : A) (C : (b : A) → a₀ ≡ b → Set) where

   J-elim-PM : (d : C a₀ refl) → (b : A) → (p : a₀ ≡ b) → C b p
   J-elim-PM d b refl = d

-- this is "Axiom K" (which is disabled in the options)
module _ (a₀ : A) (C : a₀ ≡ a₀ → Set) where

  K : (d : C refl) → (p : a₀ ≡ a₀) → C p
  K d p = {!p!}

-- Caveat:
-- judgmental equality in Agda: = but on paper: ≡
-- path type in Agda: ≡ but on paper: =

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public
infixr 4 _,_

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

{-
Exercise 5
For a given function f : A -> B, a *pointwise left inverse* is a
function g : B -> A such that (a : A) -> g (f a) = a.

Show: If f has a pointwise left inverse then, for all a,b : A, the
function ap_f {a} {b} has a pointwise left inverse. (Does the other
direction hold as well?)

Solution of the easy part:
-}

has-ptw-left-inv : {A B : Set} → (f : A → B) → Set
has-ptw-left-inv {A} {B} f = Σ (B → A) λ g → (a : A) → g (f a) ≡ a

ptw-left-inv-ap : {A B : Set} → (f : A → B) →
                  has-ptw-left-inv f →
                  {a₁ a₂ : A} → has-ptw-left-inv (ap f {a₁} {a₂})
ptw-left-inv-ap f (g , g∘f) {a₁} {a₂} =
                (λ q → (g∘f a₁ ⁻¹) ∙ ap g {f a₁} {f a₂} q ∙ g∘f a₂) ,
                λ {refl →  sym-refl (g∘f a₁) }

{-
  Exercise 6: a1 a2 : A, b1 b2 : B
  (a1 , b1) ≡ (a2 , b2) is equivalent to (a1 = a2) × (b1 = b2).

  Exercise 7:
  eqv2iso :   isEqv(f) -> isIso(f)   [easy]
  iso2eqv :  isIso(f) -> isEqv(f)   [hard]
-}

module _ (A B : Set) (g : B → A) (a b : B) where

  lemma : (pair1 pair2 : Σ A λ x → x ≡ g a) → pair1 ≡ pair2
  lemma (.(g a) , refl) (.(g a) , refl) = refl

  wrong : (pair1 pair2 : Σ A λ x → g a ≡ g b) → pair1 ≡ pair2
  wrong (x1 , p1) (x2 , p2) = {!p1!}



split-equality : {x y : A × B} → x ≡ y → (fst x ≡ fst y) × (snd x ≡ snd y)
split-equality = {!!}

combine-equalities : {x y : A × B} → (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
combine-equalities = {!!}

