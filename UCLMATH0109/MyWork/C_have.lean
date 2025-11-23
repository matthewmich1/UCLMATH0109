import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-- xₙ → a if for any ε > 0 there is N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε  -/
def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε

notation "limₙ " => sLim

/-- The sequence `1/(n+1) → 0` -/
theorem one_over_nat : limₙ (fun n => (n + 1)⁻¹) 0 :=
by
  intro ε hε --reading from sLim definition.
  dsimp
  have h : ∃ N : ℕ, N > ε⁻¹
  · exact exists_nat_gt ε⁻¹
  obtain ⟨N,hN⟩ := h
  use N
  intro n hn
  rw [sub_zero]
  have : |(n + 1 : ℝ)⁻¹| = (n + 1 : ℝ)⁻¹
  · refine abs_eq_self.mpr ?this.a
    apply le_of_lt
    exact Nat.inv_pos_of_nat
  rw [this]
  have : n+1 > ε⁻¹
  · trans (N:ℝ)
    · norm_cast
      linarith
    · exact hN
  exact inv_lt_of_inv_lt hε this
