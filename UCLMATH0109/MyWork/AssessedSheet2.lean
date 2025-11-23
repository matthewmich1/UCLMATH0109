
import Mathlib.Tactic
import UCLMATH0109.Course._2_foundations.F_nat


-- # Questions using `rfl` / `rw` (covering sections 2E and 2F of the course material)

-- 01
example (a b : ℝ) (ha : a = 0) (hb : b = a ) : b = 0 :=by
  rwa [hb]

-- 02
example : 2 + 3 - 7 = 2 * 4 - 8 :=by
  rfl

-- 03
example (a : ℕ) (ha : ∀ b, ∃ c, c * b = a) : a = 0 :=by
  specialize ha 0 --plugs in 0 into ha
  obtain ⟨c,h⟩ := ha --c wasn't a defined term so we use obtain tactic
  rw [←h]
  rfl

-- 04
example (a : ℕ) (h : a * a = a) : a * a * a * a * a = a * a * a :=by
  rwa [h,h,h]

-- 05
example (a b c : ℕ) (hab : a * b = c) (hbc : b * c = a) (hca : c * a = b) :
    c * b * a = a * b * (c * a) * (b * c) :=by
  rw [hab,hca,hbc]

/-
# Questions using our version of the natural numbers `N`

inductive N
| zero : N
| succ (n : N) : N

You can do the next few questions using `induction` as well as `rw` using the results proved in `F_nat.lean`

Look in that file for definitions of functions on N as well as useful theorems to apply.
In particular remember how we defined the `pow` function `a ^ b`

def pow : N → N → N
| _ , 0      =>   1              --  a ^ 0 = 1
| a , succ b => a * (pow a b)    --  a ^ (b + 1) = a * (a ^ b)

-/

namespace N

--- This bit of code allows us to refer to "3" in the usual way
instance : OfNat N 3 where
  ofNat := succ 2

-- 06
theorem one_pow (n : N) : 1 ^ n = 1 :=by
  induction n with
  | zero =>
    rw [zero_eq]
    rfl
  | succ n ih =>
    rw [pow_succ,ih]
    rfl


-- 07
theorem pow_add (a b c : N) : a ^ (b + c) = a ^ b * a ^ c :=by
  induction c with
  | zero =>
    rw [zero_eq,add_zero,pow_zero,mul_one]
  | succ n ih =>
    rw [add_succ,pow_succ,pow_succ,ih,mul_comm,mul_assoc,mul_comm a]


-- 08
theorem pow_mul (a b c : N) : a ^ (b * c) = (a ^ b) ^ c :=by
  induction c with
  | zero =>
    rw [zero_eq,mul_zero,pow_zero,pow_zero]
  | succ n ih =>
    rw [mul_succ,pow_succ,←ih,pow_add,mul_comm]

-- 09
theorem two_eq_succ_one : (2 : N) = succ 1 :=by
  rfl

-- 10
theorem three_eq_one_add_two : (3 : N) = 1 + 2 :=by
  rfl

-- 11
theorem two_mul (n : N) : 2 * n = n + n :=by
  rw [two_eq_succ_one, succ_mul, one_mul]

-- 12
theorem pow_three (n : N) : n ^ 3 = n * n ^ 2:=by
  rfl

theorem pow_two (n : N) : n ^ 2 = n * n:= --not an exercise but proof needed to answer question 13.
by
  rw [two_eq_succ_one,pow_succ,pow_one]

-- 13
theorem add_sq (a b : N) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=by
  rw[pow_two,pow_two,pow_two,add_mul,mul_add,mul_add,two_mul,add_mul,mul_comm b,add_assoc,add_assoc,add_assoc]


/-
We can define the Fibonacci numbers in the standard way (note that Mathlib uses a much faster equivalent definition)
-/

def Fibonacci : N → N
  | 0     => 0
  | 1     => 1
  | n + 2 => Fibonacci n + Fibonacci (n + 1)

/-
We prove a few simple results using the `rfl` tactic.
-/
lemma Fibonacci_zero : Fibonacci 0 = 0 :=by
  rfl

lemma Fibonacci_one : Fibonacci 1 = 1 :=by
  rfl

lemma Fibonacci_step (n : N) : Fibonacci (n + 2) = Fibonacci n + Fibonacci (n + 1) :=by
  rfl

-- 14
lemma Fibonacci_add_three :
    Fibonacci (n + 3) = Fibonacci n + 2 * Fibonacci (n + 1) :=by
  rw [three_eq_one_add_two,two_mul,←add_assoc,Fibonacci_step,add_assoc,←two_mul,mul_one,Fibonacci_step,add_comm,add_assoc]


-- 15
/-
Prove that if `n` is a multiple of 3, then the `n`-th Fibonacci number is even.
-/
lemma Fibonacci_three_mul (n : N) : ∃ k, Fibonacci (3 * n) = 2 * k :=by
  induction n with
  | zero =>
    rw [zero_eq,mul_zero]
    use 0
    rfl
  | succ n ih =>
    rw [succ_eq_add_one,mul_add,mul_one,Fibonacci_add_three]
    obtain ⟨a,ha⟩ := ih --2a gives first term on LHS, then we want second term on LHS
    use (a + (3 * n + 1).Fibonacci)
    rw [mul_add,←ha]


-- 16 The `induction n generalizing m` tactic is very useful here. Make sure you understand what it does.
lemma Fibonacci_add (m n : N) :
    Fibonacci (m + n + 1) = Fibonacci m * Fibonacci n + Fibonacci (m + 1) * Fibonacci (n + 1) :=by
  induction n generalizing m with
  | zero =>
    rw [zero_eq,add_zero,zero_add,Fibonacci_zero,Fibonacci_one,mul_zero,mul_one,zero_add]
  | succ n ih =>
    specialize ih (m+1)
    rw [succ_eq_add_one,add_comm n,←add_assoc, ih,add_assoc]
    rw [← two_mul,mul_one,Fibonacci_step,add_comm n,add_comm,add_comm 1,add_assoc]
    rw [←two_mul,mul_one,Fibonacci_step,add_mul,add_comm (n.Fibonacci), mul_add, add_assoc]


-- 17 A harder question on propositional logic
example (P : N → Prop) (h : ∀ n, P n ↔ ¬ (P (n + 1) ↔ P (n + 2))) :  ∀ n, P n → P (n + 3) :=by
  intro n pn
  obtain ⟨hfn,_⟩ := h n
  specialize hfn pn --
  push_neg at hfn
  cases hfn with
  | inl h' =>
    obtain ⟨hfn1,_⟩ := h (n + 1)
    --rw [add_assoc, add_assoc, ←three_eq_one_add_two,←two_mul,mul_one] at *
    specialize hfn1 h'.1
    push_neg at hfn1
    cases hfn1 with
    | inl ha =>
      obtain ⟨_,_⟩ := ha
      obtain ⟨_,_⟩ := h'
      contradiction
    | inr ha =>
      obtain ⟨_,pn3⟩ := ha
      exact pn3
  | inr h' =>
    obtain ⟨_,hr⟩ := h (n + 1)
    --rw [add_assoc, add_assoc, ←three_eq_one_add_two,←two_mul,mul_one] at *
    obtain ⟨npn1,pn2⟩ := h'
    by_contra npn3
    apply npn1; apply hr
    push_neg
    left
    constructor
    · exact pn2
    · exact npn3


/-   # Proof by structural recursion
The plain `induction` tactic only allows us to apply the induction hypothesis for `n`
while proving the case `succ n`. Sometimes we need something stronger and Lean has its
own internal version of induction called `structural recursion` built-in. This is like
strong induction in that it allows us to use the inductive hypothesis for any smaller case.

We give an example below where we use the inductive hypothesis for `n` to prove the
case of `n + 2`.

-/

theorem add_two_eq (n : N) : ∃ i j : N, n + 2 = 2 * i + 3 * j :=by
  cases n with
  | zero =>
    use 1, 0;
    rw [zero_eq, zero_add, mul_one, mul_zero, add_zero]
  | succ n =>
    cases n with
    | zero =>
      use 0, 1
      rw [zero_eq, succ_eq_add_one,  zero_add, mul_one, mul_zero, zero_add,
          three_eq_one_add_two]
    | succ n =>
      -- We now use the fact that `n` is smaller than `n + 2` and
      -- since we are in the case `n + 2` we can apply the theorem we
      -- are proving in the case `n`.
      obtain ⟨c, d, hc⟩ := add_two_eq n
      use (c + 1), d
      rw [two_mul, succ_add, succ_add, hc, ← succ_eq_add_one,
       add_succ, succ_add c, ←two_mul, succ_add,succ_add]


-- 18 define a series `mySeries` by taking the first two terms to be `1` and `3`,
-- and then each further term to be the product of the previous two terms.

def mySeries : N → N
  | 0 => 1
  | 1 => 3
  | (n + 2) => mySeries n * mySeries (n + 1)

lemma mySeries_zero : mySeries 0 = 1 := by
  rfl

lemma mySeries_one : mySeries 1 = 3 := by
  rfl

lemma mySeries_step (n : N) : mySeries (n + 2) = mySeries n * mySeries (n + 1) := by
  rfl


-- 19 State and prove a lemma in Lean which relates `mySeries` to `Fibonacci`.
-- (You may want to use the the `structural recursion` we saw in the proof of `add_two_eq` above.)

lemma mySeries_rel_to_fib (n : N) : mySeries n = 3 ^ (Fibonacci n) := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [succ_eq_add_one, succ_eq_add_one, add_assoc, ←two_mul, mul_one, Fibonacci_step, pow_add, ←mySeries_rel_to_fib, ←mySeries_rel_to_fib]
      rfl
