import Mathlib.Tactic

/-
# Not : ¬ P  (tactics: contradiction / intro / apply / exfalso / by_cases)
We would like `not P` to be the proposition that is true iff P is False

In particular if we have `P` and `¬P` in the local context then we have a `contradiction`
and from this we can prove any proposition Q
-/
example (P Q : Prop) (hp: P) (hnp: ¬ P) : Q :=
by
  contradiction -- If we have terms P and ¬ P, then the contradiction tactic solves any goal.




/-  To prove `¬ P` we need to show that assuming `P` we get a contradiction.

In Lean `¬ P` is formally defined as `P → False` so it is an implication.
We can start a proof of `¬ P` with `intro hp` and then we try to derive a contradiction.
-/

example (P : Prop) : ¬ (P ∧ ¬P):= -- aim is to get terms of P and ¬P in the local context and then use contradiction.
by
  intro h -- h is a term of type P ∧ ¬P. Now we want terms of P and ¬P in the local context.
  obtain ⟨hp,hnp⟩ := h -- hp is a term of type P and hnp is a term of type ¬P.
  contradiction




/-
Since **any** proposition `Q` follows from a contradiction we can always replace any goal
`⊢ Q` by `⊢ False` the Lean tactic for this is `exfalso`
-/
example (Q : Prop) (hf : False ) : Q := --we have a proof of false and we want a proof of proposition Q.
by
  exfalso -- changes the goal from Q to False
  exact hf
  --note: hf is already a contraction so we could've just stated contradiction instead of exfalso exact hf.

-- In our next example we could start with `intro hp`, `intro hn`
-- but these two tactics can me merged into one.
example (P : Prop) : P → ¬¬P := -- ¬¬ P is defined as (¬P → False) which is ((P → False) → False).
by
  intro hp hnp -- hp is a term of type P and hnp is a term of type ¬P. The goal is now False.
  contradiction --since we have terms of P and ¬P in the local context, contradiction solves the goal.

/-
In order to prove that `P` and `¬¬P` are equivalent we need to assume the
Law of the Excluded Middle, which says that for any proposition P we have:
 `P ∨ ¬ P`
The Lean tactic `by_cases hp : P` allows us to use this to construct a proof into
two goals where in the first we have `hp : P` and in the second we have `hp : ¬P`
-/
example (P : Prop) : ¬¬ P → P:=
by
  intro hnnp -- hnnp is a term of type ¬¬P i.e (((P → False) → False)). The goal is now P.
  by_cases h': P -- Now we have two cases. In the first we have P is true, in the second we have P is false. Goals is P in both cases.
  · exact h' -- Goal is P and h' is a term of type P so we are done.
  · contradiction -- we have hnnp is a term of type ¬¬P and h' is a term of type ¬P which are a contradiction so we are done.

/-
# True : (tactic : trivial)
`True` is the proposition that is trivially true, its proof is `trivial`
-/
example (P : Prop) : P → True :=
by
  intro _ --hp is a term of type P. The goal is now True.
  trivial --solves the goal True.



/-
# Now do exercises and examples in sheet2C.lean
-/
