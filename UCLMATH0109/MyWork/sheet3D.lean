import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example (a b x : ℕ) (h₁ : a + b = 5) (h₂ : a * b = 6) :
  x ^ 2 + 5 * x + 6 = (x + a) * (x + b) :=
by
  calc
    _ = x^2 + (a+b) * x + a*b   := by rw [←h₁,←h₂]
    _ = _                       := by ring

open Polynomial
/-
In the next example, we do a similar kind of calculation in the
ring `ℝ[X]` of polynomials over the real numbers. Prove the
formula using a `calc` block.
-/
example (a b c d : ℝ[X]) (h₁ : a^2 + b^2 = X * c) (h₂ : a * b = d) :
    (X + a^2) * (X+b^2) = X^2 * (1 + c) + d^2 := by
  calc
    _ = X ^ 2 + X * a ^ 2 + X * b ^ 2 + a ^ 2 * b ^ 2 := by ring
    _ = X ^ 2 + X * (a ^ 2 + b ^ 2) + (a * b) ^ 2     := by ring
    _ = X ^ 2 + X * (X * c) + d ^ 2                   := by rw [h₁,h₂]
    _ = X ^ 2 + X ^ 2 * c + d ^ 2                     := by ring
    _ = X ^ 2 * (1 + c) + d ^ 2                       := by ring

/-
Here is an example with inequalities.
Use `ring`, `norm_num`, `rw` and `rel` in a `calc` clock.-/
example (x y : ℝ) (hx : x > 1) (hy : 5 < y) :
  x ^ 3 + 4 * x * y - 20 > 0 := by
  calc
    _ > 1 ^ 3 + 4 * 1 * y - 20 := by rel [hx]
    _ > 1 ^ 3 + 4 * 1 * 5 - 20 := by linarith
    _ > 0                      := by linarith

/-
This last example is a proof that `x^2` is a continuous at the point `x=1`.

You should prove the `have` statement by a single `calc` block,
abd then prove the main result by a single `calc` block.
In each `calc`-block you will only need the tactics`ring`, `rw`, `rel` and `exact`.

You might find the following lemmas from Mathlib useful:
  `lt_min`
  `min_le_left`
  `min_le_right`
  `abs_add`
  `abs_mul`
-/
#check lt_min
#check lt_of_lt_of_le
#check min_le_right
#check mul_le_mul

example (x ε : ℝ) (hε : 0 < ε) :
  ∃ δ, 0 < δ ∧ (|x - 1| < δ → |x^2 - 1^2| < ε) := by
  let δ := min 1 (ε/3)
  have δpos : 0 < δ
  · apply lt_min
    · norm_num
    · linarith
  use δ
  constructor
  · exact δpos
  · intro hx
    have : |x + 1| < 3
    · calc
        _ = |(x - 1) + (1 + 1)|   := by norm_num; ring
        _ ≤ |x - 1| + |1 + 1|     := by exact abs_add (x - 1) (1 + 1)
        _ = |x - 1| + |2|         := by norm_num
        _ = |x - 1| + 2           := by norm_num
        _ < 1 + 2                 := by exact add_lt_add_right (lt_of_lt_of_le hx (min_le_left 1 (ε / 3))) 2
        _ = 3                     := by norm_num
    calc
      _ = |x ^ 2 - 1|             := by ring
      _ = |(x - 1) * (x + 1)|     := by ring
      _ = |x - 1| * |x + 1|       := by exact abs_mul (x - 1) (x + 1)
      _ < δ * 3                   := by rel [hx,this]
      _ = (min 1 (ε / 3)) * 3     := by rfl 
      _ ≤ (ε / 3) * 3             := by
        refine mul_le_mul ?h₁ ?h₂ ?c0 ?b0
        · exact min_le_right 1 (ε / 3)
        · norm_num
        · norm_num
        · linarith
      _ = ε                       := by ring
    -- Use a `calc`-block here. First factorize the left hand side,
    -- and then use `this`, `hx` and `δpos`.
