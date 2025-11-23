import Mathlib.Tactic
import Mathlib.Data.Real.Basic
/-

  # Assessed Sheet 3

Covering material from sheets 2G-H, 3A-D using the following tactics:

 `ext` `norm_num` `linarith` `ring` `apply?` `exact?` `decide`
  `refine` `convert` `congr!` `have` `calc`

In the exercises below you can always introduce new `have` statements
to give new goals that help.

-/

-- 01
example (a b : ℕ) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith


-- 02
example (A B : Set ℕ) (hA : ∀ a ∈ A, a ≤ 3) (hB : ∀ b ∈ B, b ≤ 2) : ∀ c ∈ A ∪ B, c ^ 2 ≤ 9 := by
  intro c hC
  cases hC with --we want cases c ∈ A and c ∈ B i.e split the union statement hence we use cases with
  | inl h => --want to eventually apply hA since c ∈ A i.e prove c ≤ 3
    have h : c ≤ 3
    · apply hA; exact h
    · nlinarith
  | inr h => -- want to eventually apply hB since c ∈ B i.e prove c ≤ 2
    have h : c ≤ 2
    · apply hB; exact h
    · nlinarith

/-
 # Set builder notation
Set builder notation is built up from left to right in the obvious way,
so `x ∈ {a, b, c, d}` is definitionally `x = a ∨ x ∈ {b, c, d}`
-/

example (a b c d e : ℤ) : a ∈ ({d, c, b, a, e} : Set ℤ) := by
  right; right; right; left; rfl


/- # Set.range
If `f : α → β` then `Set.range f := {x : β | ∃ y : α, f y = x}`
So if `h : x ∈ Set.range f` then `h` is definitionally `∃ y : α, f y = x`
-/

-- 03
example (f : ℤ → ℤ) (h₀ : f 0 = -1) (h₁ : f 1 = 1) (h : ∀ x, f x = -1 ∨ f x = 1) : Set.range f = {-1, 1} := by
  ext x
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := hx --set.range has a ∃ statement so we can use obtain.
    rw [←ha]
    exact h a
  · intro hx
    cases hx with --since hx states hx is either 1 or -1 we use cases hx with to consider both cases.
    | inl h =>
      refine Set.mem_range.mpr ?h.mpr.inl.a
      use 0
      rwa [h]
    | inr h =>
      refine Set.mem_range.mpr ?h.mpr.inr.a
      use 1
      rwa [h]

/-
In the same way that `succ n` is Lean for `n + 1` so `pred n` is Lean for `n - 1`

Subtraction on ℕ is defined in terms of `pred`

def Nat.pred : ℕ → ℕ
  | 0      => 0         --          0 - 1 = 0
  | succ a => a         --    (a + 1) - 1 = a


def Nat.sub : ℕ → ℕ → ℕ
  | a, 0      => a              --            a - 0 = a
  | a, succ b => pred (a - b)   --      a - (b + 1) = (a - b) - 1

Warning: subtraction in ℕ is nasty, eg `4 - 6 = 0` etc..

In particular `ℕ` is not a ring so the `ring` tactic will struggle with
subtraction in ℕ (but is great at proving identities in ℤ, ℝ, ℚ etc).

One strategy that can work in `ℕ` is to first rewrite the identity you are trying to prove
so that subtraction does not appear. Once you've done this `ring` should finish it off.

-/

-- 04
example (a b : ℕ) : a = a + b - b := by
  exact Nat.eq_sub_of_add_eq rfl


-- 05
example : ∃ (a b : ℕ), a - b  + b ≠ a := by --does a-b first then adds b. In ℕ, a-b = 0 if b ≥ a.
  use 1, 2
  trivial --trivial is quicker than norm_num

-- 06
example (m : ℕ) (h : 0 < m) : (2 * m) ^ 2 + (m ^ 2 - 1) ^ 2 = (m ^ 2 + 1) ^ 2:= by
  have h : ∃ n : ℕ, m = n + 1
  · exact Nat.exists_eq_add_of_le' h
  · obtain ⟨n,hn⟩ := h
    rw [hn,add_sq,pow_two 1,mul_one,mul_one]
    have : n ^ 2 + 2 * n + 1 - 1 = n ^ 2 + 2 * n
    · rfl
    rw [this]
    ring

-- 07 this is very easy (notice we are in `ℤ` not `ℕ`)
example (m n : ℤ) : (n ^ 2 - m ^ 2) ^ 2 + (2 * m * n) ^ 2 = (n ^ 2 + m ^ 2) ^ 2 := by
  ring

/-- A function `f : ℝ → ℝ` is continuous at `a : ℝ` iff ... -/
def Cts (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0 , ∀ x, |x - a| < δ → |f x - f a| < ε


#check half_pos -- if `0 < a` then `0 < a / 2`
#check lt_min -- if `a < b` and `a < c` then `a < min b c`
#check abs_add
#check add_lt_add

/-
08 If `f` and `g` are continuous at `a` then so is `f + g`
-/
lemma cts_add (hf : Cts f a) (hg : Cts g a):  Cts (f + g) a := by
  rw [Cts]
  rw [Cts] at hf hg
  intro ε hε
  specialize hf (ε/2) (half_pos hε)
  specialize hg (ε/2) (half_pos hε)
  obtain ⟨δf,hf1, hf2⟩ := hf
  obtain ⟨δg,hg1, hg2⟩ := hg
  use min δf δg
  constructor
  · apply lt_min hf1 hg1
  · intro x hx
    have hδf : |x - a| < δf
    · calc
      _ < min δf δg := hx --by and exact cancel out
      _ ≤ δf := min_le_left δf δg --by and exact cancel out

    have hδg : |x - a| < δg
    · calc
      _ < min δf δg := hx
      _ ≤ δg := min_le_right δf δg

    specialize hf2 x hδf
    specialize hg2 x hδg
    calc
    |(f + g) x - (f + g) a| = |f x + g x - (f a + g a)|     := by rfl
    _                       = |(f x - f a) + (g x - g a)|   := by congr! 1; ring
    _                       ≤ |f x - f a| + |g x - g a|     := by exact abs_add (f x - f a) (g x - g a)
    _                       < ε/2 + ε/2                     := by rel [hf2,hg2]
    _                       = ε                             := by ring

#check lt_div_iff' -- if `0 < c` then  `a < b / c ↔ c * a < b`
#check div_pos -- if `0 < a` and `0 < b` then `0 < a / b`
#check abs_mul

variable (c : ℝ)
#check |c|

#check div_pos
#check abs_mul
#check mul_sub
#check div_mul_cancel₀


/-
09 If `f` is continuous at `a` then so is `f * c` for any constant `c : ℝ`
Hint: consider the cases `c = 0` and `c ≠ 0` separately. Sketch the proof on paper first.
-/
lemma cts_const_mul (hf : Cts f a) (c : ℝ) : Cts (fun x ↦ c * f x) a := by
  rw [Cts]
  rw [Cts] at hf
  intro ε hε
  by_cases hc : c = 0
  · rw [hc]
    use 1
    constructor
    · norm_num
    · intro x _
      rwa [zero_mul,zero_mul,sub_self,abs_zero]
  · have h : |c| > 0
    · exact abs_pos.mpr hc
    · specialize hf (ε / |c|) (div_pos hε h)
      obtain ⟨δf,hf1,hf2⟩ := hf
      use δf
      constructor
      · exact hf1
      · intro x hx
        specialize hf2 x hx
        calc
        |c * f x - c * f a| = |c| * |f x - f a|   := by
          rw [← mul_sub, abs_mul]
        _                   < |c| * (ε / |c|)     := by
          rel [hf2]
        _                   = ε                   := by
          rw [mul_comm,div_mul_cancel₀]
          intro p
          linarith

          --field_simp --found from maths in lean book on useful links. Reduces denominators.
