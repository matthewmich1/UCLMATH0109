import Mathlib.Tactic

-- 01
example  (A B C : Type) (f : A → B) (g : B → C) (x : A) : C :=
by
  apply g
  apply f
  exact x

-- 02
example (α β γ : Type)  (g : γ → α) : (α → β) → (γ → β) :=
by
  intro f --term f is of type (alpha -> beta). The goal is now gamma -> beta. Doing intro gives a term of type gamma.
  intro x --term x is of type gamma. The goal is now beta. We have f, function from alpha to beta and g from gamma to alpha.
  apply f --goal is now alpha so we apply g. We have g: gamma -> alpha and x : gamma.
  exact (g x)

-- 03
example (A B C D : Type) (f : A  → B) (g : B → C) (h : C → D) (a : A): D :=
by
apply h
apply g
apply f
exact a

-- 04
example (A B C D E : Type)(f : A → B) (g : B → C) (_ : D → E) (i : C → E) (x : A) : E :=
by
  apply i
  apply g
  apply f
  exact x

-- 05
example (A B : Type) : ((A → B) → (A → A)) → ((A → A) → (B → A)) → ((B → A) → (B → A)) :=
by
  intro _ --_ is a term of type (A->B)->(A->A). The goal is now (A->A)->(B->A)->(B->A).
  intro _ --_ is a term of type (A->A)->(B->A). The goal is now (B->A)->(B->A).
  intro h --h is a term of type (B->A). The goal is now (B->A). We need to produce a term of type (B->A).
  exact h --h is already a term of type (B->A) so we are done.
