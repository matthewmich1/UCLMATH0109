import UCLMATH0109.Course._2_foundations.F_nat

namespace N


theorem one_pow (n : N) : 1 ^ n = 1:=
by
  induction n with
  | zero =>
    rw [zero_eq, pow_zero]
  | succ n ih =>
    rw [pow_succ, ih]
    rfl

theorem pow_add (a b c: N) : a ^ (b + c) = a ^ b * a ^ c :=
by
  induction c with
  | zero =>
    rw [zero_eq,add_zero,pow_zero,mul_one]
  | succ n ih =>
    rw [add_succ, pow_succ,pow_succ,ih,←mul_assoc,mul_comm (a),mul_assoc]


theorem pow_mul (a b c : N) : a ^ (b * c) = (a ^ b) ^ c :=
by
  induction c with
  | zero =>
    rw [zero_eq,mul_zero,pow_zero,pow_zero]
  | succ n ih =>
    rw [pow_succ,mul_succ,pow_add,ih,mul_comm]


theorem two_eq_succ_one : 2 = succ 1 :=
by
  rfl

theorem two_eq_one_add_one : 2 = 1 + 1:=
by
  rfl

theorem two_mul (n : N) : 2 * n = n + n :=
by
  induction n with
  | zero =>
    rw [zero_eq,mul_zero,add_zero]
  | succ n ih =>
    rw [mul_succ,ih,succ_eq_add_one,←add_assoc,add_comm (n+1),add_assoc,add_assoc,add_assoc, two_eq_succ_one, succ_eq_add_one]



theorem pow_two (n : N) : n ^ 2 = n * n:=
by
  rw [two_eq_succ_one,pow_succ,pow_one]

theorem add_sq (a b : N) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by
  rw [pow_two,pow_two,pow_two,mul_add,add_mul,add_mul,two_mul,add_mul,mul_comm b,add_assoc,add_assoc,add_assoc]


theorem pow_pow (a b c : N) : (a ^ b) ^ c = a ^ (b * c) :=
by
  induction c with
  | zero =>
    rw [zero_eq,pow_zero,mul_zero,pow_zero]
  | succ n ih =>
    rw [pow_succ,mul_succ,pow_add,ih,mul_comm]
