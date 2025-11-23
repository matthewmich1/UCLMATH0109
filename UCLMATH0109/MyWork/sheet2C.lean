import Mathlib.Tactic

-- 01 De Morgan's 1st law
example : ¬ (P ∨ Q) ↔  ¬P ∧ ¬ Q:=
by
  constructor
  · intro hnpq --term of type ¬(P ∨ Q) which means (P ∨ Q) → False. Goal is now ¬P ∧ ¬Q.
    constructor -- left goal is ¬P (P → False) and right goal is ¬Q (Q → False).
    · intro hp; apply hnpq --changes goal to P ∨ Q. We have a term of P.
      left; exact hp
    · intro hq; apply hnpq --changes goal to P ∨ Q. We have a term of Q.
      right; exact hq
  · intro hnpq hpq -- hnpq is a term of type ¬P ∧ ¬Q and hpq is a term of type P ∨ Q. Goal is now False.
    obtain ⟨hnp,hnq⟩:=hnpq -- hnp is a term of type ¬P and hnq is a term of type ¬Q.
    cases hpq with -- 2 cases: case 1, P is true, case 2, Q is true. Goal is False in both cases.
    | inl hp => -- we have terms of P and ¬P in the local context which is a contradiction
      contradiction
    | inr hq => -- we have terms of Q and ¬Q in the local context which is a contradiction
      contradiction

/-
In the next three examples you will need to use `by_cases` in one of the two
implications
-/

-- 02 De Morgan's 2nd law (you will need to use `by_cases` in the first implication)
example : ¬ (P ∧ Q) ↔  ¬P ∨ ¬ Q:=
by
  constructor
  · intro hnpq --goal is now ¬P ∨ ¬Q i.e (P → False) ∨ (Q → False).
    by_cases hp : P --2 cases: case 1, P is true, case 2, P is false. Goal is ¬P ∨ ¬Q.
    · right --goal is ¬Q (Q → False). We can't use left as the goal will be ¬P which we don't have, and we already assume P is true.
      push_neg at hnpq
      apply hnpq; exact hp
    · left; exact hp --in this case, hp is a term of ¬P and left makes the goal ¬P so we are done.
  · intros h hpq
    obtain ⟨_,_⟩ := hpq
    cases h with
    | inl h =>
      contradiction
    | inr h =>
      contradiction

-- 03
example : (P → Q) ↔ Q ∨ ¬P:=
by
  constructor
  · intro h -- h is a term of type (P → Q). The goal is now Q ∨ ¬P.
    by_cases hp : P --2 cases: case 1, P is true, case 2, P is false. Goal is Q ∨ ¬P.
    · left -- goal is now Q. We have a term of P and function from P to Q.
      apply h; exact hp
    · right; exact hp -- right changes goal to ¬P which is what hp is.
  · intro h hp --h is a term of type Q ∨ ¬P. The goal is now (P → Q). hp is a term of P so goal is now Q. h has or statement so use cases.
    cases h with --2 cases: case 1, Q is true, case 2, ¬P is true. Goal is Q in both cases.
    | inl hq =>
      exact hq
    | inr hnp => -- we have term hp of P and term ¬P.
      contradiction

-- 04 this can be done without `by_cases`
example : ¬(P ↔ ¬P) := -- same as ((P → ¬P) ∧ (¬P → P)) → False
by
  intro h
  obtain ⟨hf,hb⟩ := h
  apply hf
  · by_contra hp
    specialize hb hp
    contradiction
  · by_contra hp
    specialize hb hp
    contradiction


-- 05 contrapositive
example : P → Q ↔ ¬ Q → ¬P :=
by
  constructor
  · intro h hnq -- h is a term of type (P → Q) and hnq is a term of type ¬Q. The goal is now ¬P.
    by_cases hp : P --2 cases: case 1, P is true, case 2, P is false. Goal is ¬P.
    · intro _
      apply hnq; apply h; exact hp
    · exact hp -- hp is a term of ¬P and goal is ¬P so we are done.
  · intro h hp
    by_cases hq : Q
    · exact hq
    · contrapose h
      push_neg
      constructor
      · exact h
      · exact hp




/-
Lean has a built-in tactic `contrapose` that converts any goal `P → Q`
into its contrapositive

Lean also has a tactic `push_neg` for pushing negations inside expressions.

Remember this tactic for when we introduce quantifiers!
-/
-- 06
example (P Q R : Prop): (P → Q ∨ R) → (P → Q) ∨ (P → R):=
by
  contrapose
  -- Goal is: `⊢ ¬((P → Q) ∨ (P → R)) → ¬(P → Q ∨ R)`
  push_neg
  -- Goal is now : `⊢ (P ∧ ¬Q) ∧ P ∧ ¬R → P ∧ ¬Q ∧ ¬R`
  intro h
  constructor
  · exact h.1.1
  · obtain ⟨hpnq,_,hnr⟩ := h
    obtain ⟨_,hnq⟩  := hpnq
    constructor
    · exact hnq
    · exact hnr

-- 07
example (P Q : Prop): ((P → Q) → P) → P:=
by
  contrapose
  push_neg
  intro hnp
  constructor
  · intro hp
    contradiction
  · exact hnp


-- 08
example : ¬(P → Q) ↔ P ∧ ¬Q:=
by
  constructor
  · intro hnpq
    push_neg at hnpq
    exact hnpq
  · intro hpnq
    push_neg
    exact hpnq
