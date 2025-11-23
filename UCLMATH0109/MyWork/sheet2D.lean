import Mathlib.Tactic

variable (A: Type) (P Q R: A → Prop)

-- 01
example : (∀x, ∃y, P y → P x) :=
by
  intro x
  use x
  intro px
  exact px

-- 02
example (h : ∃ x, ¬ P x) : ¬ ∀ a, P a:=
by
  push_neg
  obtain ⟨x,_⟩ := h
  use x



/-
We used the tactic `push_neg` to push negations inside a goal.

We can also use it to simplify a negated hypothesis `h : ¬ P`
with `push_neg at h`
-/

-- 03
example (h : ¬ ∀ a, ¬P a)  : ∃ x, P x:=
by
  push_neg at h
  obtain ⟨x,_⟩ := h
  use x


-- 04
example : (∀ x, P x → Q x) → (∀y, Q y → R y) → (∀z, R z → P z) → (∀a, R a ↔ P a):=
by
  intro hpq hqr hrp a
  constructor
  · apply hrp a
  · intro pa
    apply hqr a; apply hpq a; exact pa


/-
If our hypothesis is `h: ∃x, ∃y,...` then `obtain ⟨x, y, hxy⟩ := h` will give us `x` and `y`

If our goal is `⊢ ∃y, ∃x, ...` we can first tell Lean what to use for `y` and then the
goal will change to `⊢ ∃ x,...`  so we can then tell it what to use for `x`
-/
-- 05
example  (h : ∃x, ∃y, P x → P y) : (∃x, ∃y, P y → P x):=
by
  obtain ⟨y,x,hp⟩ := h
  use x
  use y


-- 06
example : (∀ x, P x) → (∃x, ¬ Q x) → ∃ (a b : A), ¬ (P a → Q b):=
by
  intro hp hnq
  push_neg
  obtain ⟨b,hq⟩ := hnq
  specialize hp b
  use b
  use b



-- 07
example: (∃x, ¬Q x) → (∃ y, Q y) →
  ∃ a b, ∀ z, P z → Q a ∧ ¬(P z → Q b) :=
by
  intro hnq hq
  obtain ⟨b,h1⟩ := hnq
  obtain ⟨a,h2⟩ := hq
  use a
  use b
  intro z pz
  constructor
  · exact h2
  · push_neg
    constructor
    · exact pz
    · exact h1


-- 08
example : (∀x, ∃y, ¬(P x → P y)) → (∃u, P u) → (∃v, ¬ P v) :=
by
  intro h hpu
  push_neg at h
  obtain ⟨u,_⟩ := hpu
  specialize h u
  obtain ⟨v,huv⟩ := h
  use v
  exact huv.2


-- 09
example : (¬∀a, (P a → Q a)) ↔ ∃x, (¬Q x ∧ P x):=
by
  constructor
  · intro h
    push_neg at h
    obtain ⟨x,h1⟩ := h
    use x
    constructor
    · exact h1.2
    · exact h1.1
  · intro h
    push_neg
    obtain ⟨a,h2⟩ := h
    use a
    constructor
    · exact h2.2
    · exact h2.1


variable (C : A → A → Prop)
-- 10 The no barber theorem
-- You can do this using `by_cases` on something..
-- But you can also do it without using `by_cases`
example : ¬∃ b, ∀ a, C b a ↔ ¬ C a a :=
by
  push_neg
  intro b
  use b
  by_cases hcb : C b b
  · left
    constructor
    · exact hcb
    · exact hcb
  · right
    constructor
    · exact hcb
    · exact hcb
