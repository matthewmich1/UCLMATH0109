import Mathlib.Tactic

/-
Use the tactics described in _2_foundations/B_or_and_imp.lean
to complete the following proofs.
-/


-- 01 `∧` is symmetric
example (h : P ∧ Q) : Q ∧ P :=
by
  constructor -- This breaks the goal Q ∧ P into two goals: Q and P.
  · exact h.2
  · exact h.1


-- 02 `∨` is symmetric
example (h : P ∨ Q) : Q ∨ P :=
by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

-- 03
example (h: (P ∨ Q) ∧ (P ∨ R)) : P ∨ (Q ∧ R):= --Goal is either P is true or Q ∧ R is true given that P ∨ Q is true and P ∨ R is true.
by
  obtain ⟨hpq, hpr⟩:=h --hpq : P ∨ Q and hpr : P ∨ R.
  cases hpq with -- splits P ∨ Q into two cases: one where P is true and one where Q is true.
  | inl hp => -- hp : P and our goal here is P ∨ (Q ∧ R)
    left
    exact hp
  | inr hq => -- We have hq : Q and our goal here is P ∨ (Q ∧ R).
    cases hpr with --splits P ∨ R into two cases: one where P is true and one where R is true.
    | inl hp => --case where P is true. Since our goal is P ∨ (Q ∧ R), and we have hp : P, we are done.
      left
      exact hp
    | inr hr => --case where R is true. Since our goal is P ∨ (Q ∧ R), and we have hq : Q and hr : R, we can use constructor to prove Q ∧ R.
      right --we have proofs of both Q and R so we can prove Q ∧ R. right changes the goal to Q ∧ R.
      constructor --and statement hints use constructor to break the goal Q ∧ R into two goals: Q and R.
      · exact hq
      · exact hr


/-
Each of `∧, ∨, →` is a binary operation on `Prop` (Why?).

In order to understand compound propositions such as  `P ∧ Q → P ∧ R → P ∨ Q ∨ R`
(without using lots of brackets) we need to know how Lean parses such expressions.

Let's start with the single operation `→` and work out how Lean makes sense of the
expression: `P → Q → R`

There are two possiblities for how this could be defined:

  **left-associative**, so `P → Q → R` would be defined as `(P → Q) → R` or
  **right-associative**, so `P → Q → R` would be defined as `P → (Q → R)`?

But which is it?

You will face many similar situations and the key to deciphering such
expressions is to use the `#check` command and/or the `Infoview`.
-/
variable (P Q R S : Prop)
#check (P → Q) → R -- (P → Q) → R : Prop
#check P → (Q → R) -- P → Q → R : Prop -- Look no brackets!
/-
So `→` is right-associative, since when we add brackets on the right Lean
removes them in the Infoview. This tells us that they were not required.
-/
#check P → (Q → (R → S)) -- P → Q → R → S : Prop

-- 04 `→` is transitive
theorem imp_is_trans : (P → Q) → (Q → R) → (P → R):=
by
-- We can `intro` multiple terms at the same time
  intro hpq hqr hp -- hpq : P → Q, hqr : Q → R and hp : P. The goal is now R.
  apply hqr -- don't need to use apply hp as we have apply hqr. The goal is now Q.
  apply hpq -- The goal is now P.
  exact hp

/-
Our last proof was a `theorem` rather than an `example` so what's the difference?

An `example` is anonymous (i.e. it has no name) so we can't refer to it.
A `theorem` needs to have a name (and it must be unique)

(We can also have a `lemma` which, as far as Lean is concerned, is a theorem.)

With a theorem or lemma we can use `#check` to see what its statement says.
-/
#check imp_is_trans
/-
In our next example our goal is to prove `P → Q → P ∧ Q`.

Since this involves two binary operations, `→` and `∧`, we have another potential
source of confusion.

If you can't see why there could a possible problem, consider the sum

    `2 + 4 + 6 / 3 = 8`

We know this evaluates to `8` because of the BIDMAS rules which say that you do `/`
before `+` (formally we say `/` has **higher precedence** than `+`).

We don't usually write `2 + 4 + (6 / 3) = 8` because the brackets are not needed
once you know the rules of BIDMAS.

Lean follows the same basic convention. Each binary operation is either left- or
right-associative, and it also has a value associated to it that allows Lean to know
which to do first (i.e. the operation with the higher value has higher precedence).

So which has higher precedence `→` or `∧`? Again, we can work it out systematically.

This time we will use the Infoview (rather than #check)
-/
-- 05
example : P → Q → P ∧ Q:=
by
/-
Click here. Now move you cursor to hover over the Infoview.
The goal is `⊢ P → Q → P ∧ Q`
If you hover over the `∧` in the goal you will see that the drop-down
information says `P ∧ Q : Prop`, so there are implied brackets `(P ∧ Q)`.

We deduce that Lean gives `∧` higher precedence than `→` (it did `∧` first).

If you now hover over each of the `→` symbols in the goal you can deduce that Lean
parses this expression as `P → (Q → (P ∧ Q))`

Lean follows the convention that it only displays brackets if they are required
(i.e. if they change the default meaning of an expression)
-/
  intro hp hq -- hp : P and hq : Q. The goal is now P ∧ Q. This hints that we should use `constructor`.
  constructor
  · exact hp
  · exact hq

/-
In the next example our goal is `⊢ P ∨ Q ∨ R` so we first need to know whether
`∨` is left- or right-associative.
-/

-- 06
example (hpq: P ∨ Q) (hqr: Q ∨ R) : P ∨ Q ∨ R :=
by -- Place your cursor here and then hover over the
-- two `v` symbols in the Infoview goal `⊢ P ∨ Q ∨ R`
-- Can you work out where the brackets should go? Brackets should be placed around Q ∨ R since the statement is right associative.
  cases hpq with -- splits P ∨ Q into two cases: one where P is true and one where Q is true.
  | inl hp => -- hp : P and our goal here is P ∨ (Q ∨ R)
    left
    exact hp
  | inr hq => -- We have hq : Q and our goal here is P ∨ (Q ∨ R).
    right -- goal here is now Q ∨ R.
    cases hqr with -- splits Q ∨ R into two cases: one where Q is true and one where R is true.
    | inl hq =>
      left
      exact hq
    | inr hr =>
      right
      exact hr


-- So `∨` is right-associative
#check P ∨ (Q ∨ R) -- P ∨ Q ∨ R : Prop
/-
Most of the binary operations you will have seen previously are associative:
for example `1 + (2 + 3) = (1 + 2) + 3` in `ℕ` and `a*(b*c) = (a*b)*c` in a group.

In fact `∨` and `∧` are both associative, but these are theorems not definitions!
-/
-- 07 `v` is associative
theorem or_is_assoc : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R):=
by
  constructor -- 2 cases to prove an `↔` statement.
  · intro h -- term of type (P ∨ Q) ∨ R. The goal is now P ∨ (Q ∨ R).
    cases h with -- splits (P ∨ Q) ∨ R into two cases: one where P ∨ Q is true and one where R is true.
    | inl h => -- case where P ∨ Q is true. We have h : P ∨ Q and our goal is P ∨ (Q ∨ R). We use h again to split into two cases.
      cases h with -- splits P ∨ Q into two cases: one where P is true and one where Q is true.
      | inl h => --case where P is true. Here, h is a term of type P and our goal is P ∨ (Q ∨ R) so we are done.
        left; exact h
      | inr h => --case where Q is true. Here, h is a term of type Q and our goal is P ∨ (Q ∨ R).
        right --goal is now Q ∨ R.
        left -- goal is now Q.
        exact h --We have a term h in Q so we are done.
    | inr h => -- case where R is true. Here, h is a term of type R and our goal is P ∨ (Q ∨ R).
      right
      right
      exact h

  · intro h -- term of type P ∨ (Q ∨ R). Goal is now (P ∨ Q) ∨ R.
    cases h with -- splits P ∨ (Q ∨ R) into two cases: one where P is true and one where Q ∨ R is true.
    | inl h => -- case where P is true. h is a term of type P.
      left; left; exact h
    | inr h => -- case where Q ∨ R. Goal is (P ∨ Q) ∨ R.
      cases h with -- splits Q ∨ R into two cases: one where Q is true and one where R is true.
      | inl h => -- case where Q is true. h is a term of type Q. Goal is (P ∨ Q) ∨ R.
        left; right; exact h
      | inr h => --case where R is true. h is a term of type R. Goal is (P ∨ Q) ∨ R.
        right; exact h

/-
  `∧` is also defined to be right-associative
-/
#check P ∧ (Q ∧ R) -- P ∧ Q ∧ R : Prop
-- 08 `∧` is associative
theorem and_is_assoc : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R):=
by
  constructor
  · intro h -- of type (P ∧ Q) ∧ R. The goal is now P ∧ (Q ∧ R).
    constructor -- breaks the goal P ∧ (Q ∧ R) into two goals: P and Q ∧ R.
    · exact h.1.1
    · constructor -- breaks the goal Q ∧ R into two goals: Q and R.
      · exact h.1.2
      · exact h.2

  · intro h -- of type P ∧ (Q ∧ R). The goal is now (P ∧ Q) ∧ R.
    constructor -- two goals: P ∧ Q and R.
    · constructor -- two goals: P and Q.
      · exact h.1
      · exact h.2.1
    · exact h.2.2


/-
The next example is something we will use a lot.

As mathematicians we have lots of theorems that say things
like `if P and Q  are both true then R is true`.

Typically in Lean we express this as the equivalent proposition:
`P → Q → R`
-/
-- 09
example : (P ∧ Q → R) ↔ (P → Q → R) :=
by
  constructor -- 2 cases to prove an `↔` statement. First case: (P ∧ Q → R) → P → Q → R.
  · intro h -- term of type P ∧ Q → R. Goal is now P → Q → R.
    intro hp hq --Goal is now R.
    apply h
    --- Our goal is `⊢ P ∧ Q` and we have `hp : P` and `hq : Q`
    --- Rather than using `constructor` we can use `exact ⟨hp,hq⟩`
    --- (This is like `obtain` but in reverse)
    exact ⟨hp,hq⟩
  · intro h -- term of type P → Q → R. Goal is now P ∧ Q → R. We prove R given a term of type P ∧ Q.
    intro hpq -- term of type P ∧ Q. Goal is now R.
    apply h -- 2 goals now: P,Q. hpq is a term of type P and Q, so we can use hpq.1 to get a term of type P.
    exact hpq.1
    exact hpq.2




-- 10
example : (P ∨ Q → R) ↔ (P → R) ∧ (Q → R):=
by
  constructor
  · intro h
    constructor
    · intro hp
      apply h
      left; exact hp
    · intro hq
      apply h
      right; exact hq
  · intro h
    intro hpq
    cases hpq with
    | inl hp =>
      apply h.1; exact hp
    | inr hq =>
      apply h.2; exact hq
