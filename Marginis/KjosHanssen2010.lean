import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real


theorem page5_display3_equals2 (b:ℝ): (2:ℝ)^(b+1) * 4^(b-1) = 2^(3*b-1):=
/-
Formal verification of
https://arxiv.org/pdf/1408.2850.pdf
Page 5
3rd displayed equation
Second "equals" sign
-/
  (calc
  2^(3*b-1) = 2^(b+1 + 2*(b-1))     := by ring_nf
  _         = 2^(b+1) * 2^(2*(b-1)) := Real.rpow_add zero_lt_two _ _
  _         = 2^(b+1) * (2^2)^(b-1) := by rw [Real.rpow_mul zero_le_two _ _];simp only [Real.rpow_two]
  _         = 2^(b+1) * 4^(b-1)     := by norm_num).symm


theorem page7_display4_lt2 (b c : ℝ) (h: b < c) :
(2:ℝ)^(-b) + 2^(-c) < 2^(-(b-1)) :=
/-
Formal verification of
https://arxiv.org/pdf/1408.2850.pdf
Page 7
4th displayed equation
Second "<" sign
-/
  have : -c < -b         := neg_lt_neg h
  have : (2:ℝ)^(-c) < 2^(-b) := (Real.rpow_lt_rpow_left_iff one_lt_two).mpr this
  calc
  _ < 2^(-b) + 2^(-b) := (Real.add_lt_add_iff_left (2 ^ (-b))).mpr this
  _ = 2 * 2^(-b)      := by ring
  _ = 2^1 * 2^(-b)    := by simp only [pow_one]
  _ = 2^(1+(-b))      := by
    let Q := @Real.rpow_add 2 (by exact zero_lt_two) 1 (-b)
    rw [Q]
    simp only [pow_one, Real.rpow_one]
  _ = 2^(-(b-1))      := by ring_nf

/-
Page 8
5th displayed equation
Inequality
proved in paper_bound'' below
-/

theorem bound_of_nonneg (p:ℝ) : 0 ≤ 4*p*(p-1) + 1 := calc
  _ ≤ (2*p-1)*(2*p-1) := mul_self_nonneg _
  _ = 4*(p*p) - 4*p + 1 := by ring
  _ = _                 := by ring

theorem numerator_bound (p:ℝ) : 4*(p*(1-p)) ≤ 1 :=
  calc
  _ = - (4*p*(p-1))         := by ring
  _ = - (4*p*(p-1) + 1) + 1 := by ring
  _ ≤ -0 + 1                := add_le_add_right (neg_le_neg (bound_of_nonneg p)) 1
  _ = 1                     := by ring

theorem le_div {a b c : ℝ} (ha: 0<a) (g: a*b ≤ c) : b ≤ c/a :=
  ((le_div_iff' ha).mpr) g

theorem the_bound (p:ℝ) : p*(1-p) ≤ 1/4 :=
  le_div zero_lt_four (numerator_bound p)

theorem mul_self_bound {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : p*p ≤ 1 := calc
_ ≤ p * 1 := mul_le_mul_of_nonneg_left h1 h0
_ ≤ 1 * 1 := mul_le_mul_of_nonneg_right h1 zero_le_one
_ = 1     := one_mul 1


theorem sq_bound {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : p^2 ≤ 1 :=
  calc
  _ = p^(1+1)     := by ring_nf;simp only [Real.rpow_two]
  _ = p^(1) * p^1 := Real.rpow_add' h0 (by linarith)
  _ = p*p         := by rw [Real.rpow_one]
  _ ≤ 1           := mul_self_bound h0 h1


theorem cube_bound {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : p^(3:ℝ) ≤ 1 :=
  calc
  _ = p^(2+1)     := by ring_nf
  _ = p^2 * p^1   := Real.rpow_add' h0 (by linarith)
  _ = p^2 * p     := by rw [Real.rpow_one];simp only [Real.rpow_two]
  _ ≤ 1 * p       := mul_le_mul_of_nonneg_right (sq_bound h0 h1) (h0)
  _ = p           := one_mul _
  _ ≤ 1           := h1


theorem cube_bound' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : (1-p)^(3:ℝ) ≤ 1 :=
  cube_bound (sub_nonneg.mpr h1) (sub_le_self 1 h0)

theorem paper_bound {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
  (1-p)^(3:ℝ) + p^(3:ℝ) ≤ 2 := calc
  (1-p)^(3:ℝ) + p^3 ≤ (1-p)^3 + 1 := add_le_add_left  (cube_bound  h0 h1) _
  _             ≤ 1 + 1       := add_le_add_right (cube_bound' h0 h1) _
  _             = 2 := by ring


theorem paper_bound' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
  p * (1-p) * ((1-p)^(3:ℝ) + p^(3:ℝ)) ≤ 1/2 :=
calc
_ ≤ p * (1-p) * 2 := mul_le_mul_of_nonneg_left (paper_bound h0 h1) (mul_nonneg h0 (sub_nonneg.mpr h1))
_ ≤ (1/4) * 2     := mul_le_mul_of_nonneg_right (the_bound _) (by linarith)
_ = _             := by ring_nf

example : (0:ℝ)^(0:ℝ) = 1 := by exact Real.rpow_zero 0
example : (0)^(0:ℕ) = 1 := by exact rfl

theorem paper_bound'' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
  (1-p)^(4:ℝ) * p + p^(4:ℝ) * (1-p) ≤ 1/2 :=
calc
  _ = (1-p)^((3:ℝ)+1) * p         + p^((3:ℝ)+1) * (1-p)     := by ring_nf
  _ = (1-p)^(3:ℝ) * (1-p)^(1:ℝ) * p + (p^(3:ℝ) * p^1) * (1-p) := by
      rw [Real.rpow_add']
      simp;left;
      by_cases H : p = 0
      . subst H
        simp
        refine Real.zero_rpow ?_
        have : (3:ℝ) + 1 = 4 := by exact three_add_one_eq_four
        rw [this]
        exact Ne.symm (NeZero.ne' 4)

      refine Real.rpow_add_one ?h.hx 3;
      tauto
      linarith;
      have : (3:ℝ) + 1 = 4 := by exact three_add_one_eq_four
      rw [this]
      exact Ne.symm (NeZero.ne' 4)
  _ = (1-p)^(3:ℝ) * (1-p)   * p + (p^(3:ℝ) * p) * (1-p)   := by
    simp only [Real.rpow_one, pow_one]
  _ = p * (1-p) * ( (1-p)^(3:ℝ) + p^(3:ℝ))                := by
    ring_nf
  _ ≤ _                                             := paper_bound' h0 h1


/- Bottom of page 7: -/
/- Caution is needed since 3/2=1 and 3*(1/2)=0 over ℕ. -/
#eval 3/2
#eval 3*(1/2)

open Nat
theorem choose_two (n:ℕ) : 2 * choose n 2  = n*(n-1) := match n with
  |0 => rfl
  |Nat.succ n =>
    calc
    _ = 2 * (choose n 1 + choose n 2)    := rfl
    _ = 2 * (choose n 1) + 2* choose n 2 := Nat.mul_add 2 (choose n 1) (choose n 2)
    _ = 2 * (n) + (n*(n-1))              := by rw[choose_two,choose_one_right]
    _ = 2 * (n) + (n*n - n*1)            := by rw [Nat.mul_sub_left_distrib]
    _ = 2 * (n) + (n*n - n)              := by ring_nf
    _ = (2 * (n) + (n*n)) - n            := (Nat.add_sub_assoc (Nat.le_mul_self n) _).symm
    _ = (n*(n) + n) + n - n              := by ring_nf
    _ = (n*(n) + n)                      := Nat.add_sub_cancel (n * n + n) n
    _ = (n+1) * n                        := by linarith
    _ = (n+1) * ((n+1) - 1)              := rfl
    _ = Nat.succ n * (Nat.succ n - 1)    := by linarith


theorem choose_two_formula (n:ℕ) : choose n 2  = (n*(n-1))/2 := calc
choose n 2 = choose n 2 * 2 / 2 := (Nat.mul_div_cancel _ zero_lt_two).symm
_ = 2 * choose n 2 / 2 := by ring_nf
_ = n*(n-1) / 2 := by rw[choose_two]

theorem caution : ∃ n : ℕ, (n*(n-1))/2 ≠ n*((n-1)/2) := by {exists 2}

theorem page7_bottom (n:ℕ) : choose n 2 * choose 4 2 = 3*n*(n-1) := calc
  _ = choose n 2 * 6       := rfl
  _ = 3 * (2 * choose n 2) := by ring
  _ = 3 * (n*(n-1))        := by rw [choose_two]
  _ = _                    := by ring


/-
Page 2
1st displayed inequality
-/
open Classical

noncomputable def one_on (P : Prop) : ℕ := ite P 1 0

theorem one_on_inequality (x a : ℕ) : a * one_on (a ≤ x) ≤ x := by
  by_cases h : (a ≤ x)

  have : one_on (a ≤ x) = 1 := if_pos h
  rw [this]
  simp
  exact h

  have : one_on (a ≤ x) = 0 := if_neg h
  rw [this]
  simp

theorem real_one_on_inequality (x a : ℝ) (g : 0 ≤ x) : a * one_on (a ≤ x) ≤ x := by
  by_cases h : (a ≤ x)

  have : one_on (a ≤ x) = 1 := if_pos h
  rw [this]
  simp
  exact h

  have : one_on (a ≤ x) = 0 := if_neg h
  rw [this]
  simp
  exact g
