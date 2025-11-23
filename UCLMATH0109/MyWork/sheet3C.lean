import Mathlib.Tactic

namespace Sheet3C


/-- xₙ → a if for any ε > 0 there is N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε  -/
def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε

notation "limₙ " => sLim

/--
`Cts f a` means that `f` is continuous at `a` -/
def Cts (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε

/-
Fill in the proof of the `have` statament, to complete the proof that `|x|` is a
continuous function of `x`. -/
-- 01
example (a : ℝ): Cts (fun x ↦ |x|) a :=
by
  intro ε hε
  dsimp
  use ε
  constructor
  · assumption
  · intro x hx
    have h : |(|x| - |a|)| ≤ |x - a|
    · exact abs_abs_sub_abs_le_abs_sub x a
    exact lt_of_le_of_lt h hx


/-
Have a look at the following proof that `10*x` is a continuous function of `x`.
There are three `have` statements. Fill in the proof of each of these, using any tactics which you know.
-/
-- 02
example (a : ℝ) : Cts (fun x ↦ 10*x) a :=
by
  intro ε hε
  dsimp
  let δ := ε / 10 --need a proof of δ > 0
  have : δ > 0
  · ring
    linarith
  use δ
  constructor
  · exact this
  · intro x hx
    rw [←mul_sub, abs_mul]
    have : |(10:ℝ)| = 10
    · norm_num
    rw [this]
    have : ε = 10 * δ
    · ring
    rw [this]
    linarith


/-
The sLim_sandwich theorem: if  `xₙ  → a` and `zₙ → a` and for all n ∈ ℕ , `xₙ ≤ yₙ ≤ zₙ`  then `yₙ → a`  -/
-- 03
theorem sLim_sandwich (hx : limₙ x a) (hz : limₙ z a) (hb : ∀ n, x n ≤ y n ∧ y n ≤ z n) :
    limₙ y a :=
by
  intro ε hε
  obtain ⟨Nx,hNx⟩ := hx ε hε
  obtain ⟨Nz,hNz⟩ := hz ε hε
  use max Nx Nz
  intro n hn
  have h1 : Nx ≤ n
  · exact le_of_max_le_left hn
  have h2 : Nz ≤ n
  · exact le_of_max_le_right hn
  specialize hNx n h1
  specialize hNz n h2
  have identity : ∀ (a b c : ℝ), |a - b| < c ↔ a - b < c ∧ b - a < c
  · exact fun a b c ↦ abs_sub_lt_iff
  obtain ⟨_,_⟩ := hb n
  rw [identity] at *
  constructor
  · linarith
  · linarith

end Sheet3C
