import Mathlib.Tactic

-- 01  (1 mark)
example (P Q : Prop) : P ∧ Q ∧ ¬ P → ¬ Q := by
  intro h
  obtain ⟨_,_,_⟩ := h
  contradiction

-- 02 (1 mark)
example (a b c : ℕ) (h : b ≤ a) : a - b + c = c + a - b:= by
  refine Eq.symm (Nat.sub_eq_of_eq_add ?h)
  have : a - b + c + b = a + c
  · sorry
  rw [this]
  ring

-- 03  (2 marks)
example (n : ℕ) : n = 0 ∨ ∃ k : ℕ, k < n := by
  right
  have hk : ∃ k : ℕ, k ≤ n
  · use 0
    linarith
  obtain ⟨k,_⟩ := hk
  use k
  sorry

-- 04  (3 marks)
example (n : ℕ) (P : ℕ → Prop) (h₁ : ∀ k, P (2 * k) → P (2 * k + 1)) :
    P (6 * n) → P (6 * n + 1) := by
  specialize h₁ (3 * n)
  rw [←mul_assoc] at h₁
  exact h₁


-- 05 (3 marks)
lemma helper (n : ℕ) : 2 * (n + 1) - 1 = 2 * n + 1 := by
  rw [two_mul]
  have : n + 1 + (n + 1) - 1 = n + 1 + n
  · rfl
  rw [this,add_comm,← add_assoc,←two_mul]

-- 06  (4 marks)
def oddSquares : ℕ → ℕ
| 0 => 0
| n + 1 => 3 * (2 * n + 1)^2 + oddSquares n

/- State and prove the theorem that for any `n : ℕ`,
 `oddSquares n = n * (2 * n - 1)*(2 * n + 1)`. -/
theorem oddsqridentity (n : ℕ) : oddSquares n = n * (2 * n - 1)*(2 * n + 1) := by
  cases n with
  | zero =>
    rw [oddSquares,zero_mul,zero_mul]
  | succ n =>
    rw [oddSquares, oddsqridentity]
    sorry

/-- A function `f : ℝ → ℝ` is continuous at `a : ℝ` iff ... -/
def Cts (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0 , ∀ x, |x - a| < δ → |f x - f a| < ε


-- 07 (6 marks)
example (n : ℕ): Cts (fun x => x ^ n) 0 := by
  -- we have |x| < δ => |x^n| < ε. So we want to choose δ^n = ε.
  intro ε hε
  dsimp
  use ε ^ (1 / n)
  have : ε ^ (1 / n) > 0
  · sorry
  constructor
  · trivial
  · intro x hx
    have hxn: |x ^ n - 0 ^ n| = |x| ^ n
    · sorry
    rw [hxn]
    rw [zero_pow, sub_zero] at *
    have ha : |x| ^ n < ε
    · sorry
    exact ha
    sorry
