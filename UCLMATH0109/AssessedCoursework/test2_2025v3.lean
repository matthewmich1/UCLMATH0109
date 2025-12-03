import Mathlib

/-
The questions in this test are on a structure `R` defined below.

Elements of `R` have the form `⟨x, y⟩`, where `x` and `y` are both in `Fin 2`.
This means that `R` has four elements which can be written as follows:
  `⟨0, 0⟩`, `⟨0, 1⟩`, `⟨1, 0⟩`, `⟨1, 1⟩`.
-/
@[ext] structure R where
  x : Fin 2
  y : Fin 2

#check R.ext -- R.ext (x y : R) : x.x = y.x → x.y = y.y → x = y
#check R.ext_iff -- R.ext_iff (x y : R) : x = y ↔ x.x = y.x ∧ x.y = y.y

namespace R


/-
We define a zero element of `R` to be `0 = ⟨0, 0⟩`, and we define addition of elements of `R` by
  `⟨x, y⟩ + ⟨x', y'⟩ = ⟨x + x', y + y'⟩`.
(addition in `Fin 2` is defined modulo `2`, so that `1 + 1 = 0` in `Fin 2`).
We'll also define a one element `1 = ⟨1, 0⟩` and another element `α = ⟨0, 1⟩`.
-/
@[simps] instance : Zero R := ⟨⟨0,0⟩⟩
@[simps] instance one : One R := ⟨⟨1,0⟩⟩
@[simps] def α : R := ⟨0,1⟩
@[simps] instance : Add R where
  add a b := ⟨a.x + b.x, a.y + b.y⟩

/-- If `x : Fin 2` then either `x = 0` or `x = 1`. -/
lemma cases_fin_two (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl


-- # 1 (4 marks)
-- prove that every element of `R` is in the set `{0, 1, α, α + 1}`.
lemma cases_R (a : R) : a ∈ ({0, 1, α, α + 1} : Set R) := by
  /-
  Hint:
  Given `a : R` you can obtain `x, y : Fin 2` such that `a = ⟨x, y⟩`.
  You can then use `R.ext_iff` and `cases_fin_two` given above.
  -/
  sorry

/-
We define a multiplication operation on `R` by the formula below,
and we prove that these operations make `R` into a commutative semi-ring
(a semi-ring is like a ring except that we have not defined a subtraction operation or additive inverses.
The word *commutative* means that `a * b = b * a` for all elements `a b : R`).

-/
@[simps] instance mul : Mul R where
  mul a b := ⟨a.x * b.x + a.y * b.y, a.x * b.y + b.x * a.y + a.y * b.y⟩

@[simps!] instance : CommSemiring R where
  add_assoc _ _ _       := by ext <;> simp [add_assoc]
  zero_add _            := by ext <;> simp
  add_zero _            := by ext <;> simp
  nsmul n a             := ⟨n * a.x, n * a.y⟩
  nsmul_zero _          := by ext <;> simp
  nsmul_succ _ _        := by ext <;> simp [add_mul]
  left_distrib _ _ _    := by ext <;> dsimp <;> ring_nf
  right_distrib _ _ _   := by ext <;> dsimp <;> ring_nf
  zero_mul _            := by ext <;> simp
  mul_zero _            := by ext <;> simp
  one_mul _             := by ext <;> simp
  mul_one _             := by ext <;> simp
  mul_comm _ _          := by ext <;> dsimp <;> ring_nf
  add_comm _ _          := by ext <;> dsimp <;> ring_nf
  mul_assoc _ _ _       := by ext <;> dsimp <;> ring_nf
  natCast n             := ⟨n,0⟩
  natCast_zero          := rfl
  natCast_succ _        := by ext <;> simp



--# 2 (1 mark)
@[simp] lemma two_eq_zero : (2 : R) = 0 := sorry

-- # 3 (3 marks)
/-
Define a semiring homomorphism `φ : R →+* R`, which takes every element `a : R` to `a ^ 2`.
You need to check the following axioms:
  * `φ 0 = 0`,
  * `φ 1 = 1`,
  * `φ (a * b) = (φ a) * (φ b)` for all elements `a b : R`,
  * `φ (a + b) = (φ a) + (φ b)` for all elements `a b : R`.
The last of these follows from the lemma `two_eq_zero` above.
-/
def φ : R →+* R where
  toFun a   := a ^ 2
  map_zero' := sorry
  map_one'  := sorry
  map_mul'  := sorry
  map_add'  := sorry


-- # 4 (3 marks)
/--
Prove that the cube of every non-zero element of `R` is `1`.
-/
lemma pow_three_of_nonzero {a : R} (ha : a ≠ 0) : a ^ 3 = 1 := by
  /-
  Hint : you can use `cases_R` to answer this question.
  -/

  sorry

/--
Two elements of `R` are equal if and only if their sum is `0`.
-/
lemma eq_iff_add_eq_zero (a b : R) : a = b ↔ a + b = 0 := by
  obtain (rfl | rfl | rfl | rfl) := cases_R a <;>
  obtain (rfl | rfl | rfl | rfl) := cases_R b <;>
  simp [R.ext_iff]


-- # 5 (5 marks)
/--
Let `ψ : R →+* R` be any semi-ring homomorphism (not necessarily the one defined inquestion 4.
Prove that `ψ` is injective.)
-/
lemma injective (ψ : R →+* R) : Function.Injective ψ := by
  /-
  Hint:
  Suppose `ψ a = ψ b` but `a ≠ b`.
  By `eq_iff_add_eq_zero` and `pow_three_of_nonzero`,
  we have `ψ ((a + b) ^ 3) = ψ 1`.
  Since `ψ` is a ring homommorphism, this simplifies to `(ψ a + ψ b) ^ 3 = 1`.
  Since `ψ a = ψ b` we have `(2 * ψ a) ^ 3 = 1`.
  Then using `two_eq_zero` we get `0 = 1` which is false.
  -/

  sorry

-- # 6 (4 marks)
-- Define a multiplicative inverse operation for `R` by giving
-- an instance of `Inv` for `R`.
-- State and prove a lemma that the product of any non-zero
-- element of `R` with its multiplicative inverse is `1`.
-- (The lemma `pow_three_of_nonzero` may be useful here.)
