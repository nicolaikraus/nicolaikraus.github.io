{-
    INTRODUCTION TO HOMOTOPY TYPE THEORY
        Midlands Graduate School 2021
              Nicolai Kraus

Exercises 1: You can use this file if you want to
do the exercises in Agda. Below is some code to get
you started.
-}

{-# OPTIONS --without-K #-}

open import Agda.Primitive

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

variable
  i j : Level
  A B : Set
  C : A → Set

-- postulate
--  funext : (f g : (a : A) → C a) → ((a : A) → f a ≡ g a) → f ≡ g

sym : {a b : A} → a ≡ b → b ≡ a
sym refl = refl

symsym : {a b : A} → (p : a ≡ b) → sym (sym p) ≡ p
symsym refl = refl

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public
infixr 4 _,_

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

split-equality : {x y : A × B} → x ≡ y → (fst x ≡ fst y) × (snd x ≡ snd y)
split-equality = {!!}

combine-equalities : {x y : A × B} → (fst x ≡ fst y) → (snd x ≡ snd y) → x ≡ y
combine-equalities = {!!}

-- are the above functions inverse to each other?
