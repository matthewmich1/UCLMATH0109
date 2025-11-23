import Mathlib.Tactic

/-

A `Dedekind cut` is a partition of the rationals `(A , Aᶜ)` such that both A and Aᶜ are
nonempty with the following properties:

1)  A is a down-set: if x < y and y ∈ A then x ∈ A;

2)  A has no maximum element: if x ∈ A there exists y ∈ A with x < y.

One way of constructing the real numbers from ℚ is as Dedekind cuts.

We identify a real number `r` with the cut `(A, Aᶜ)` where `A = {x ∈ ℚ | x < r}`

-/
/--
Dedekind cut
-/
@[ext] -- two Dedekind cuts D = E iff D.A = E.A
structure Dedekind where
  A         : Set ℚ
  nonempty  : A.Nonempty
  nonempty' : Aᶜ.Nonempty
  down      : ∀ ⦃x y⦄, x < y → y ∈ A → x ∈ A
  no_max    : ∀ ⦃x⦄, x ∈ A → ∃ y ∈ A, x < y

-- the @[ext] label produces the following two results for free:
#check Dedekind.ext
#check Dedekind.ext_iff

namespace Dedekind
notation "𝔻" => Dedekind

/- All our results will now be in the Dedekind namespace -/
/-
We open a named section to explain what we are trying to prove (we will prove
some basic results in this section hence the name).
-/
section basics
variable {D : 𝔻}
variable {x y : ℚ}
/-
The use of a section allows us to introduce variables into the local context
 that will vanish once the section ends.
-/
/-- If `D = (A , Aᶜ)` is a Dedekind cut with `x ∈ A` and `y ∈ Aᶜ` then `x < y`-/
lemma lt_of_cut (hx : x ∈ D.A) (hy : y ∈ D.Aᶜ) : x < y := by
  by_contra h
  push_neg at h
  have : y ∈ D.A
  · cases lt_or_eq_of_le h with
    | inl hxy => exact D.down hxy hx
    | inr heq => rw [heq]; exact hx
  contradiction



#check D.A         -- D.A : Set ℚ
#check D.nonempty  -- D.nonempty : Set.Nonempty D.A
#check D.nonempty' -- D.nonempty' : Set.Nonempty D.Aᶜ
#check D.down      -- D.down : ∀ ⦃x y : ℚ⦄, x < y → y ∈ D.A → x ∈ D.A
#check D.no_max    -- D.no_max : ∀ ⦃x : ℚ⦄, x ∈ D.A → ∃ y, y ∈ D.A ∧ x < y


/-- We can order Dedekind cuts with `D ≤ E` iff `D.A ⊆ E.A` -/
instance : LE 𝔻 where
  le := fun D E => D.A ⊆ E.A

lemma le' : D ≤ E ↔ D.A ⊆ E.A :=by rfl

/-- We can define `<` on Dedekind cuts by `D < E` iff `D ≤ E` and `D ≠ E`-/
instance : LT 𝔻 where
  lt := fun D E => D ≤ E ∧ ¬ E ≤ D

/-- `D < E` iff `D.A` is a proper-subset of `E.A` -/
lemma lt' : D < E ↔ D.A ⊂ E.A :=by rfl

/-- D < E iff ∃ x ∈ E.A \ D.A -/
lemma lt_iff_exists : D < E ↔ ∃ x, x ∈ E.A \ D.A:= by
  rw [lt']
  constructor
  · intro h
    obtain ⟨_, hne⟩ := h
    have : ∃ x, x ∈ E.A ∧ x ∉ D.A := Set.not_subset.mp hne
    obtain ⟨x, hxE, hxD⟩ := this
    use x
    constructor
    · exact hxE
    · exact hxD
  · intro ⟨x, hxE, hxD⟩
    constructor
    · intro y hy
      by_contra hny
      have : x ∈ D.A := D.down (lt_of_cut hxE hny) hy
      contradiction
    · intro h
      exact hxD (h hxE)
end basics

/-
We now establish that Dedekind cuts form a `Preorder`.

class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

-/
instance : Preorder 𝔻 where
  le_refl := by
    intro _ _ h
    exact h
  le_trans := by
    intro _ _ _ ha hb _ hc
    exact hb (ha hc)

/--
𝔻 contains a copy of the rational numbers given by the embedding `rat`
-/
def rat (q : ℚ) : 𝔻 :=by
  use {x : ℚ | x < q}
  · use q - 1
    norm_num
  · use q
    norm_num
  · dsimp
    intro y hy1 hy2 hy3
    exact gt_trans hy3 hy2
  · simp only [Set.mem_setOf_eq]
    intro x hx
    use x + (q - x) / 2
    constructor
    · linarith
    · linarith


@[simp]
lemma rat' (q : ℚ) : (rat q).A = {x : ℚ | x < q} := rfl

/-- The map `rat` is an order embedding: i.e. it is injective and `rat p ≤ rat q ↔ p ≤ q`-/
def Rat : ℚ ↪o 𝔻 where
  toFun := rat
  inj' := by
    intro p q h
    have hA : (rat p).A = (rat q).A := by rw [h]
    simp only [rat'] at hA
    have hpq : p ≤ q --use proof by contradiction
    · by_contra hnpq
      push_neg at hnpq
      -- If q < p, pick z with q < z < p using exists_between
      obtain ⟨z, hqz, hzp⟩ := exists_between hnpq --found exists_between in Mathlib
      -- Then z ∈ {x : ℚ | x < p} but z ∉ {x : ℚ | x < q}
      have hz_in : z ∈ {x : ℚ | x < p} := hzp
      have hz_notin : z ∉ {x : ℚ | x < q} := by refine Set.nmem_setOf_iff.mpr ?hz_notin.a; linarith
      rw [hA] at hz_in
      contradiction
    -- Prove q ≤ p by symmetric argument
    have hqp : q ≤ p := by
      by_contra hnqp
      push_neg at hnqp
      obtain ⟨z, hpz, hzq⟩ := exists_between hnqp
      have hz_in : z ∈ {x : ℚ | x < q} := hzq
      have hz_notin : z ∉ {x : ℚ | x < p} := by refine Set.nmem_setOf_iff.mpr ?hz_notin2.a; linarith
      rw [←hA] at hz_in
      contradiction
    linarith

  map_rel_iff' := by
    intro p q
    constructor
    · -- foward proof: rat p ≤ rat q  → p ≤ q
      intro h
      dsimp at h
      rw [le'] at h
      rw [rat', rat'] at h
      by_contra hnpq
      push_neg at hnpq
      obtain ⟨z, hqz, hzp⟩ := exists_between hnpq
      have hz_in : z ∈ {x : ℚ | x < p} := hzp
      have hz_notin : z ∉ {x : ℚ | x < q} := by refine Set.nmem_setOf_iff.mpr ?_; linarith
      have : z ∈ {x : ℚ | x < q} := h hz_in
      contradiction
    · -- backward proof: p ≤ q → rat p ≤ rat q
      intro h
      dsimp
      rw [le']
      intro x hx
      simp only [rat']
      rw [rat'] at hx
      exact gt_of_ge_of_gt h hx


instance : Zero 𝔻 where
zero := rat 0

/--
There is a Dedekind cut corresponding to √n for each n (we already have these for
0, 1 so we start from 2 here)
-/
def root_n_add_two (n : ℕ) : 𝔻 :=by
  use { x : ℚ | x^2 < (n + 2) ∨ x < 0}
  · use 0
    left
    have h : (0 : ℚ) ^ 2 < n + 2
    · have : 0 < n + 2
      · have hn : 0 ≤ (n : ℚ) := Nat.cast_nonneg n; linarith
      linarith
    exact h
  · use (n + 2 : ℚ)
    intro h
    cases h with
    | inl hl => -- aim: contradict hl by proving (n+2)² ≥ n+2
        have h_ge0 : (0 : ℚ) ≤ n + 2
        · have : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n; linarith
        have h_ge1 : (1 : ℚ) ≤ n + 2 := by linarith
        have hn : (n + 2 : ℚ) * 1 ≤ (n + 2) * (n + 2) := mul_le_mul_of_nonneg_left h_ge1 h_ge0
        have : (n + 2 : ℚ) ≤ (n + 2) ^ 2
        · calc
            (n + 2 : ℚ) = (n + 2) * 1 := by ring
            _ ≤ (n + 2) * (n + 2) := by exact hn
            _ = _ := by ring
        linarith
    | inr hr => -- aim: contradict n+2 < 0 by showing 0 ≤ n+2
        have : (0 : ℚ) ≤ n + 2
        · have : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n; linarith
        linarith
  · intro x y hxy hy
    cases hy with
    | inl h => -- y² < n+2 and x < y ⇒ x² < n+2 or x < 0
      by_cases h1 : x < 0
      · right; exact h1
      · left
        have hxy_sq : x^2 < y^2 -- need to prove 0 < y - x and 0 < y + x
        · have h_pos1 : 0 < y - x := by linarith
          have h_pos2 : 0 < y + x := by linarith
          have : y ^ 2 - x ^ 2 = (y - x) * (y + x) := by ring
          have hdiff : y ^ 2 - x ^ 2 > 0
          · calc
              _ = (y - x) * (y + x) := by rw [this]
              _ > 0 * (y + x) := (mul_lt_mul_iff_of_pos_right h_pos2).mpr h_pos1
              _ = 0 := by ring
          linarith
        linarith
    | inr h => -- y < 0 and x < y ⇒ x < 0
      right; exact lt_trans hxy h
  · intro x hx
    cases hx with
    | inl h =>
      by_cases hx_neg : x < 0
      · use 0
        constructor
        · left
          have : (0 : ℚ) ^ 2 < n + 2 := by linarith
          exact this
        · linarith
      · push_neg at hx_neg
        use (x + (n + 2)) / 2
        constructor
        · left
          have h_bound : ((x + (n + 2)) / 2) ^ 2 < n + 2
          · sorry
          exact h_bound
        · sorry
    | inr h =>
      use x / 2
      constructor
      · right
        linarith
      · linarith 


/-
If `S : Set 𝔻` is nonempty and bounded above then it has a supremum defined
by taking the union of cuts in S.
-/
noncomputable
instance : SupSet 𝔻 where
  sSup :=by
    intro S
    by_cases h : S.Nonempty ∧ BddAbove S
    · use  ⋃ d ∈ S, d.A
      · obtain ⟨D, hD⟩ := h.1
        obtain ⟨x, hx⟩ := D.nonempty
        use x
        simp only [Set.mem_iUnion, exists_prop]
        use D, hD
      · obtain ⟨E, hE⟩ := h.2
        obtain ⟨y, hy⟩ := E.nonempty'
        use y
        intro h
        simp only [Set.mem_iUnion] at h
        obtain ⟨D0, h⟩ := h
        obtain ⟨hD, hyD⟩ := h
        have hDE : D0.A ⊆ E.A := hE hD
        exact hy (hDE hyD)
      · intro x y hxy hy
        simp only [Set.mem_iUnion] at *
        obtain ⟨D, hD, hyD⟩ := hy
        use D, hD
        exact D.down hxy hyD
      · intro x hx
        simp only [Set.mem_iUnion] at *
        obtain ⟨D, hD, hxD⟩ := hx
        obtain ⟨y, hyD, hxy⟩ := D.no_max hxD
        use y
        constructor
        · use D, hD
        · exact hxy
-- If S is ∅ or not bounded above we still need to return something sensible
    · exact 0

#check dif_pos -- These can be used to simplify a function defined using `by_cases` or `if then else`
#check dif_neg

-- You can't do this question without first completing the previous one!
lemma sSup' (S : Set 𝔻) (h1 : S.Nonempty) (h2: BddAbove S) : (sSup S).A = (⋃ d ∈ S, d.A) :=by
  have h : S.Nonempty ∧ BddAbove S := ⟨h1, h2⟩
  rw [sSup]
  sorry


#check IsLeast
#check upperBounds
#check IsLUB

/--
`𝔻` is complete: any nonempty set of Dedekinds cuts that is bounded above
  has a least upper bound-/
theorem complete_lub (S : Set 𝔻) (hne: S.Nonempty) (hupb: BddAbove S) :
    IsLUB S (sSup S) :=by
  constructor
  · intro D hD
    rw [le']
    intro x hx
    rw [sSup' S hne hupb]
    simp only [Set.mem_iUnion]
    use D, hD
  · intro E hE
    rw [le']
    intro x hx
    rw [sSup' S hne hupb] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨D, hD, hxD⟩ := hx
    have : D ≤ E := hE hD
    rw [le'] at this
    exact this hxD
