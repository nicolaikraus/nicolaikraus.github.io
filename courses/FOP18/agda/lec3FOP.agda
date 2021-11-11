{- 
  Mathematical Foundations of Programming (G54FOP)
  Nicolai Kraus
  Lecture 3, 7 Feb 2018

  ====================
  INTRODUCTION TO AGDA
  ====================

  Your G54FPP project could involve Agda. If you want.

  Btw, text in {- -} is a comment. So is text after --.

  links to help you install and learn Agda:
  http://wiki.portal.chalmers.se/agda/pmwiki.php
  http://agda.readthedocs.io/en/latest/getting-started/index.html
  https://github.com/agda/agda

  Agda standard library:
  https://github.com/agda/agda-stdlib
  
  Some key combinations, where C is ctrl,
  i.e. C-c C-l means:
    press control and keep it pressed,
    press and release c,
    press and release l,
    release control.
  C-c C-l   load file, replace ? by hole
  C-c C-,   show goal
  C-c C-.   show goal and input type
  C-c C-n   normalise expression
  C-c C-space   give current hole input to Agda
  see links above for more

  I recommend using a monospace font.
-}

module lec3FOP where

  data ℕ : Set where     -- type: \bN
    zero : ℕ
    suc : ℕ → ℕ          -- type: \to or \->
                         -- (or just use ->) 

  infix 6 _+_
  _+_ : ℕ → ℕ → ℕ        -- the arguments go where _ is
  zero + n = n
  (suc m) + n = suc (m + n)  

  {- type of equalities on natural numbers *which
     we need to prove*. Some equalities can be hard
     to prove, so we cannot assume that Agda would
     find them automatically! -}
  infix 3 _==_
  data _==_ : (m n : ℕ) → Set where
    refl : {m : ℕ} → m == m

  suc-lem : {m n : ℕ} → m == n → suc m == suc n
  suc-lem refl = refl

  +-is-associative : (k m n : ℕ)
      → k + (m + n) == (k + m) + n
  +-is-associative zero m n = refl
  +-is-associative (suc k) m n =
      suc-lem (+-is-associative k m n)

  {- Next: implement the language of expressions
     from the lecture
     This language was given by a BNF:
     E:= t | f | z | s E | p E | iz E | if E then E else E
  -}

  data Expr : Set where
    t : Expr
    f : Expr
    z : Expr
    s : Expr → Expr
    p : Expr → Expr
    iz : Expr → Expr
    if_then_else_ : Expr → Expr → Expr → Expr

  -- denotational semantics from last week:
  -- ⟦_⟧ : Expr → S       type: \[[_\]]
  -- S was {True, False, 0, 1, 2, ..., ⊥}

  data Bool : Set where
    True : Bool
    False : Bool

  data S : Set where
    bool : Bool → S
    number : ℕ → S
    ⊥ : S

  -- Here we go:
  ⟦_⟧ : Expr → S
  ⟦ t ⟧ = bool True
  ⟦ f ⟧ = bool False
  ⟦ z ⟧ = number zero
  ⟦ s e ⟧ with ⟦ e ⟧
  ⟦ s e ⟧ | number n = number (suc n)
  ⟦ s e ⟧ | _ = ⊥
  ⟦ _ ⟧ = ⊥  -- not what we want, but
             -- at least Agda accepts it.
             -- Exercise: complete this definition.











