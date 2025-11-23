import Mathlib.Tactic
/-

  # Assessed Sheet 1

-/

-- Questions on functions and `Type`s
-- 01
example (α : Type) : α → α → α :=by
  intro _ a; exact a

-- 02
example (α β γ : Type) (f : α → β) (g : β → γ) : α → γ :=by
  intro a --a is a term of type α. The goal is now γ.
  apply g --goal is now β.
  exact (f a) -- f maps terms of type α to terms of type β. We have a term a in α so f a is a term in β.

-- 03
example (α β α' β' : Type) (f : α → α') (g : β' → β) : (α' → β') → (α → β) :=by
  intro h --h is a term of type (α' -> β'). The goal is now α -> β.
  intro a --a is a term of type α. The goal is now β.
  apply g --Now our goal is β'. h is function from α' to β' so applying h gives us a term in β'.
  apply h --Now our goal is a'. We have f : α -> α' and a : α.
  exact (f a)

-- 04
example (α β γ : Type) : (α → β → γ → γ) → (γ → α → β → β ) → (β → γ → α → α) :=by
  intro _ _ _ _ j   -- f is a term of type (α → β → γ → γ). The goal is now (γ → α → β → β ) → (β → γ → α → α).
  exact j

-- 05 Fill in the first sorry in this example to be a function from `α` to `β` and then complete it
example (α β γ : Type) (f : α → γ) (g : γ → β) : α → β :=by
  intro a --a is a term of type α. The goal is now β.
  apply g --Now our goal is γ. We have f : α -> γ and a : α, so f a is a term of type γ.
  exact (f a)


-- Questions on `Prop`s
-- 06
example (P : Prop) : P → P → P :=by
  intro _ p; exact p

-- Rather than repeating `P Q R : Prop` etc in every question, we can declare them as variables here.
variable (P Q R : Prop)

-- 06
example : P ∧ Q ∧ R → R ∧ P :=by
  intro h --h is a term of type P ∧ Q ∧ R. The goal is now R ∧ P.
  constructor --This breaks the goal R ∧ P into two goals: R and P.
  · exact h.2.2 --h.2 is a term of type Q ∧ R so we do .2 again to get the right term of Q ∧ R which is R. Second goal is P.
  · exact h.1 --h.1 is a term of type P so we are done.

-- 07
example : P ∨ Q ∨ R → ¬P → R ∨ Q :=by
  intro hpqr hnp -- hpqr is term of type P ∨ Q ∨ R and hnp is term of type ¬ P. Goal is R ∨ Q.
  cases hpqr with
  | inl hp => --case 1: hp is term of P. We also have a term of ¬P.
    contradiction
  | inr hqr => -- case 2: hqr is a term of Q ∨ R. Goal is R ∨ Q.
    cases hqr with -- 2 cases: case 1, hq is a term of Q, case 2, hr is a term of R. Goal is R ∨ Q.
    | inl hq =>
      right; exact hq
    | inr hr =>
      left; exact hr


-- 08 Fill in the first sorry to state `not (not (not P)) implies not P` then complete the proof.
example : ¬¬¬P → ¬P :=by
  intro h -- h is a term of type ¬¬¬P which is ((P → False) → False) → False. Goal is P → False.
  intro hp --term of tyoe P. Goal is now False.
  apply h
  intro hnp -- term of type (P → False). Goal is false.
  apply hnp; exact hp


-- 09
example : ¬(P ∨ ¬Q) ∨ R → (Q → P → R) :=by
  intro h _ hp -- h is ((P ∨ (Q → False)) → False) ∨ R.
  cases h with
  | inl hnpnq => --hnpnq is term of ((P ∨ (Q → False)) → False). Goal is R.
    exfalso
    apply hnpnq
    left; exact hp
  | inr hr =>
    exact hr


-- 10
example : P → P ∧ P ∨ P :=by
  intro hp --hp is a term of type P. The goal is now (P ∧ P) ∨ P.
  right --changes goal to P which is what hp is.
  exact hp


-- 11
example : P ∧ Q ∧ R → Q ∧ R ∧ P :=by
  intro h -- h is a term of type P ∧ Q ∧ R. The goal is now Q ∧ R ∧ P.
  constructor
  · exact h.2.1 --goal here is Q. h.2 is (Q ∧ R) so h.2.1 gives us Q.
  · constructor --changes goal from R ∧ P to two goals: R and P.
    · exact h.2.2
    · exact h.1


-- 12
example : P → Q → P ∧ Q → True :=by
  intro _ _ _; trivial


-- 13 State and prove `P and False` implies `Q`
example : (P ∧ False) → Q :=by
  intro h --h is a term of type P ∧ False. The goal is now Q.
  exfalso --changes goal from Q to False. h is a term of type False
  exact h.2


-- Questions on quantifiers
-- 14
example : ∃ n : ℕ, 3 * n = 12 :=by
  use 4


-- 15
example (a : X) : ∃ x, x = a :=by --x is term of type X (hover mouse over x to see this)
  use a


-- 16
example : ∃ n : ℕ, ∀ m, n ≠ m + 1 :=by --intuitively n = 0 works.
  use 0
  intro m --goal is 0 ≠ m + 1, which means (0 = m + 1) → False
  by_contra h
  contradiction


-- 17
example : ¬∃ n : ℕ, ∀ m, n ≠ m :=by
  push_neg
  intro n
  use n


-- 18
example (P : ℕ → Prop) (h₂ : ∀ n, P n → P (2 * n)) (h₁ : P 1) : P 32 :=by
  apply h₂ 16
  apply h₂ 8
  apply h₂ 4
  apply h₂ 2
  apply h₂ 1
  exact h₁


-- 19 State and prove: `for every natural number n there exists a natural number m that n < m`
-- (To complete the proof you could use `exact lt_add_one n` which says that `n < n + 1`)
example : ∀ n : ℕ, ∃ m : ℕ, n < m :=by
  intro n -- ∃ in goal hints to use tactic 'use value' - this value subs in for m and updates goal.
  use n + 1
  exact lt_add_one n

-- 20
example (P : ℕ → Prop) (h : ¬∃ n, ∀ a b, n < a → n < b → P a → P b ) :
  ∀ n, ∃ m, n < m ∧ (P n ↔ ¬P m) :=by
  push_neg at h
  intro n
  obtain ⟨a,b,k⟩  := h n
  by_cases hn : P n
  · use b
    constructor
    · exact k.2.1
    · constructor
      · intro _
        exact k.2.2.2
      · intro _; exact hn

  · use a
    constructor
    · exact k.1
    · constructor
      · intro pn _
        apply hn
        exact pn
      · intro pa
        obtain ⟨_,h1⟩ := k
        obtain ⟨_,h2⟩ := h1
        obtain ⟨h3,_⟩ := h2
        contradiction
