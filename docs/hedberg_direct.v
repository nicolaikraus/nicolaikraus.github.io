(** A theorem by Michael Hedberg states that any type with a decidable equality
also satisfies uniqueness of identity proofs:

Michael Hedberg, "A coherence theorem for Martin-Loef's type theory". 
In: J. Functional Programming (1998).

This Coq file contains a short and direct proof of Hedberg's theorem, as well 
as a slightly improved variant.

The original proof makes use of the fact that every "parameterized endofunction"
f : (x y : A) -> (x ~~> y) -> (x ~~> y)
(where x ~~> y is the identity type) has a left inverse. This means that f is 
injective, so if it is constant as well, x ~~> y cannot have more than one element. 
On the other hand, from the assumption that equality on A is decidable, it is 
possible to construct exactly the necessary constant endofunction.

One formalization of this proof in Agda by Nils Anders Danielsson can be found at
http://www.cse.chalmers.se/~nad/listings/equality/Equality.Decidable-UIP.html *)

(** The definition of the identity type, together with some elementary properties, 
are taken from Andrej Bauer's github (slightly modified).
See github.com/andrejbauer, 
file Homotopy/UnivalentFoundations/HomotopyDefinitions.v *)

Unset Automatic Introduction.

Inductive paths {A} : A -> A -> Type := idpath : forall x, paths x x.

Notation "x ~~> y" := (paths x y) (at level 70).

Hint Resolve @idpath.

Ltac path_induction :=
  intros; repeat progress (
    match goal with
      | [ p : _ ~~> _ |- _ ] => induction p
      | _ => idtac
    end
  ); auto.

Definition concat {A} {x y z : A} : (x ~~> y) -> (y ~~> z) -> (x ~~> z).
Proof.
  path_induction.
Defined.

Notation "p @ q" := (concat p q) (at level 60).

Definition opposite {A} {x y : A} : (x ~~> y) -> (y ~~> x).
Proof.
  path_induction.
Defined.

Notation "! p" := (opposite p) (at level 50).

Lemma opposite_left_inverse A (x y : A) (p : x ~~> y) : idpath y ~~> (!p @ p).
Proof.
  path_induction.
Defined.



(** The proof we want to give is based on the observation that the statement 
"A has decidable equality" looks pretty much like
a weakened variant of "A is contractible" (i.e. "A has h-level 0"). 
But from h-level 0, it is easy to prove h-level 2 (uip). Here, a slight
modification of that proof works! *)

Open Scope type_scope.

Definition decidable A := A + (A -> False).

Definition dec_equ A := forall x y : A, decidable (x ~~> y).

(** compare this to
Definition contractible A := exists x : A, forall y : A, x ~~> y *)

Definition proof_irrelevant A := forall x y : A, x ~~> y.

Definition uip A := forall x y : A, proof_irrelevant (x ~~> y).

(** We first prove a (local) lemma, namely that any identity proof is equal
to one that can be extracted from the decidability term dec. Of course, this 
is already nearly the complete proof. We do that as follows:
Given x and y in A and a proof p that they are equal, we check what 
dec "thinks" about x and y (as well as x and x). If dec tells us they 
are not equal, we get an obvious contradiction. Otherwise, dec precisely
says that they are in the same "contractible component", so we can just
go on as in the proof that the h-level is upwards closed.

With this lemma at hand, the rest is immediate. *)

Theorem hedberg A : dec_equ A -> uip A.
Proof.
  intros A dec x y.
  
  assert ( 
    lemma :
    forall proof : x ~~> y,  
    match dec x x, dec x y with
    | inl r, inl s => proof ~~> !r @ s
    | _, _ => False
    end
  ).
  Proof.
    induction proof.
    destruct (dec x x) as [pr | f].
    apply opposite_left_inverse.
    exact (f (idpath x)).
  
  intros p q.
  assert (p_given_by_dec := lemma p).
  assert (q_given_by_dec := lemma q).
  destruct (dec x x).
  destruct (dec x y).
  apply (p_given_by_dec @ !q_given_by_dec).
  contradiction.
  contradiction.
Qed.

(** Note that uip is equivalent to h-level 2 and, in particular, 
it would be fairly easy to show that there is not only a proof that
p equals q, but even a unique one. We do not do this here. *)

(** Christian Sattler has pointed out to me that the above proof can actually
be used to show the following slightly stronger version of Hedberg's theorem, 
stating that "local decidability implies local uip": *)

Theorem hedberg_strong A (x : A) : 
  (forall y : A, decidable (x ~~> y)) -> 
  (forall y : A, proof_irrelevant (x ~~> y)).
Proof.
  intros A x dec y.
  
  assert ( 
    lemma :
    forall proof : x ~~> y,  
    match dec x, dec y with
    | inl r, inl s => proof ~~> !r @ s
    | _, _ => False
    end
  ).
  Proof.
    induction proof.
    destruct (dec x) as [pr | f].
    apply opposite_left_inverse.
    exact (f (idpath x)).
  
  intros p q.
  assert (p_given_by_dec := lemma p).
  assert (q_given_by_dec := lemma q).
  destruct (dec x).
  destruct (dec y).
  apply (p_given_by_dec @ !q_given_by_dec).
  contradiction.
  contradiction.
Qed.

(* by Nicolai Kraus *)