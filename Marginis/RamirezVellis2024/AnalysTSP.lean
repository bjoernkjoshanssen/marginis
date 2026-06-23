/-
Copyright (c) 2026 Austin Anderson and Tony Ou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Austin Anderson, Tony Ou
-/

import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Function
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Init.Data.Int
import Init.Prelude
import Lean.Meta.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi

--The ultimate goal is to show there exists no rectifiable path
--covering ℚ×ℚ ∩ [0,1]×[0,1] in the plane, as an example
--of a bounded countable set for which no solution to the
--analyst's travelling salesman problem exists. We build
--countability of the set from elementary principles and use a
--compactness argument.

variable (A : Set ℚ)

lemma nat_to_int_eq (a b : ℕ) : (a = b) → ((↑a : ℤ) = (↑b : ℤ)) := by {
  exact fun a_1 ↦ congrArg Nat.cast a_1
}

lemma flip_neg (a b : ℤ) : (a = -b) ↔ (-a = b) := by {
  exact Iff.symm neg_eq_iff_eq_neg
}

--z.sign is funky
def neg_fit_part (z : ℤ) : ℕ :=
  match z with
  | 0 => 0
  | 1 => 0
  | (-1) => 1
  | _ => 2 --should never occur

def neg_fit (z : ℤ) : ℕ :=
  neg_fit_part (Int.sign z)

#eval neg_fit (-12)

lemma neg_fit_eq_zero_or_one (z : ℤ) : (neg_fit z = 0) ∨ (neg_fit z = 1) := by {
  cases z with
  | ofNat n =>
    have h : (Int.sign (Int.ofNat n) = 0) ∨ (Int.sign (Int.ofNat n) = 1) := by
      cases n with
      | zero => simp
      | succ n => simp
    cases h with
    | inl ha =>
      apply Or.inl
      unfold neg_fit
      rw [ha]
      exact rfl
    | inr h =>
      apply Or.inl
      unfold neg_fit
      rw [h]
      exact rfl
  | negSucc a =>
    apply Or.inr
    unfold neg_fit
    simp
    rfl
}


lemma sign_nonneg_iff_natAbs_eq (z : ℤ) :
(z.natAbs = z) ↔ ((z.sign = 0) ∨ (z.sign = 1)) := by {
  apply Iff.intro
  · intro h
    cases z with
    | ofNat x =>
      cases x with
      | zero => simp
      | succ y => simp
    | negSucc a =>
      rw [Int.natAbs_negSucc a] at h
      have h2 : Int.negSucc a < 0 := by
        apply Int.negSucc_lt_zero a
      rw [← h] at h2
      contradiction
  · intro h
    cases h with
    | inl h1 =>
      rw [Int.sign_eq_zero_iff_zero] at h1
      rw [h1]
      simp
    | inr h2 =>
      rw [Int.sign_eq_one_iff_pos] at h2
      have h3 : 0 ≤ z := by exact Int.le_of_lt h2
      apply (Int.natAbs_of_nonneg h3)
}


lemma neg_fit_iff_pos (z : ℤ) : (z.natAbs = z) ↔ ((neg_fit z) = 0) := by {
  apply Iff.intro
  · cases hna : z.natAbs
    · intro h0; rw [← h0]; rfl
    · intro ha; rw [← ha]; rfl
  · intro hpa
    cases hna : z.natAbs with
    | zero =>
      simp [Int.natAbs_eq_zero.mp hna]
    | succ n =>
      unfold neg_fit at hpa
      unfold neg_fit_part at hpa
      have hs : (z.sign = 0) ∨ (z.sign = 1) := by
        cases z with
        | ofNat a =>
          cases a with
          | zero => simp
          | succ b => simp
        | negSucc a =>
          simp at hpa
      have hs2 : (z.natAbs = z) := by
        exact (sign_nonneg_iff_natAbs_eq z).mpr hs
      rw [← hs2]
      rw [hna]
}

--#eval ((-4).sign)
--#eval (neg_fit (-4))

def spread_fun (z : ℤ) : ℕ := 2*z.natAbs + neg_fit z
#eval spread_fun (-12)

theorem spread_fun_inj : spread_fun.Injective := by {
  unfold Function.Injective
  intro a1 a2
  unfold spread_fun
  intro h
  cases h1: neg_fit a1
  cases h2: neg_fit a2
  have h1b : a1.natAbs = a1 := by
    rw [← neg_fit_iff_pos] at h1
    exact h1
  have h2b : a2.natAbs = a2 := by
    rw [← neg_fit_iff_pos] at h2
    exact h2
  rw [h1] at h
  rw [h2] at h
  simp at h
  rw [← h1b]
  rw [← h2b]
  exact congrArg Nat.cast h
  rename_i n
  exfalso  --wish for WLOG symmetric argument
  have hzo : (neg_fit a2 = 0) ∨ (neg_fit a2 = 1) := by
    exact neg_fit_eq_zero_or_one a2
  rcases hzo with hzo | ho
  · rw [h2] at hzo
    absurd hzo
    simp
  · rw [h1] at h
    rw [ho] at h
    simp at h
    have hodd : (Odd (2*a2.natAbs + 1)) := by
      simp
    rw [← h] at hodd
    exact absurd hodd (by simp)
  rename_i n1
  · cases h2 : neg_fit a2
    · have hzo2 : (neg_fit a1 = 0) ∨ (neg_fit a1 = 1) := by
        exact neg_fit_eq_zero_or_one a1
      rcases hzo2 with hzo2 | ho2
      · rw [h1] at hzo2
        absurd hzo2
        simp
      · rw [h2] at h
        rw [ho2] at h
        simp at h
        have hodd2 : (Odd (2*a1.natAbs + 1)) := by
          simp
        rw [h] at hodd2
        exact absurd hodd2 (by simp)
    · rename_i n2 -- branch succ n2
      have ha1 : (a1 = a1.natAbs) ∨ (a1 = -↑(a1.natAbs)) := by
        apply Int.natAbs_eq a1
      have hn1 : neg_fit a1 = 1 := by
        have h01 := neg_fit_eq_zero_or_one a1
        rcases h01 with h01 | h01
        · rw [h1] at h01; simp at h01
        · exact h01
      have hn2 : neg_fit a2 = 1 := by
        have h02 := neg_fit_eq_zero_or_one a2
        rcases h02 with h02 | h02
        · rw [h2] at h02; simp at h02
        · exact h02
      have ha1not0 : ¬(neg_fit a1 = 0) := by
        rw [hn1]
        simp
      have ha1notl : ¬(a1 = a1.natAbs) := by
        intro h
        have h0 : neg_fit a1 = 0 := by
          rw [← neg_fit_iff_pos, ← h]
        rw [hn1] at h0
        contradiction
      have ha1r : a1 = -↑a1.natAbs := by
        rcases ha1 with ha1 | ha1
        · rw [← ha1] at ha1notl
          absurd ha1notl
          rfl
        · exact ha1
      clear h1 h2 --copy part of above for ha2r
      have ha2 : (a2 = a2.natAbs) ∨ (a2 = -↑(a2.natAbs)) := by
        apply Int.natAbs_eq a2
      have ha2not0 : ¬(neg_fit a2 = 0) := by
        rw [hn2]
        simp
      have ha2notl : ¬(a2 = a2.natAbs) := by
        intro h
        have h0 : neg_fit a2 = 0 := by
          rw [← neg_fit_iff_pos, ← h]
        rw [hn2] at h0
        contradiction
      have ha2r : a2 = -↑a2.natAbs := by
        rcases ha2 with ha2 | ha2
        · rw [← ha2] at ha2notl
          absurd ha2notl
          rfl
        · exact ha2
      clear ha1 ha2 ha1notl ha2notl
      rw [hn1, hn2] at h
      have ha1rb : a1.natAbs = -a1 := by
        rw [flip_neg a1.natAbs a1]
        rw [← ha1r]
      have ha2rb : a2.natAbs = -a2 := by
        rw [flip_neg a2.natAbs a2]
        rw [← ha2r]
      simp at h
      apply nat_to_int_eq at h
      rw [ha1rb] at h
      rw [ha2rb] at h
      simp at h
      exact h
}

lemma spread_fun_inj_explicit (a b : ℤ) : (spread_fun a = spread_fun b) → (a = b) := by {
  intro h
  have h2 : spread_fun.Injective := by
    exact spread_fun_inj
  unfold Function.Injective at h2
  apply h2
  exact h
}


variable (B : Set ℤ)

theorem int_countable : Set.Countable B := by {
  apply (Set.countable_iff_exists_injOn).mpr
  use spread_fun
  apply Set.injOn_of_injective
  apply spread_fun_inj
}

--We'll use triangular numbers for the diagonal function.
lemma infant_Gauss (n : ℕ) : 2*(∑ x ∈ Finset.range (n+1), x)  = n*(n+1) := by {
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ]
    simp [add_comm]
    rw [Nat.mul_add, hn]
    ring
}

def diag_fun (a : ℕ×ℕ) : ℕ := ((∑ x ∈ Finset.range (a.1+a.2+1), x) + a.2)

lemma mul_2_both_sides (a b : ℕ) : a = b → 2*a = 2*b := by {
  exact fun a_1 ↦ congrArg (HMul.hMul 2) a_1
}

lemma n_sq_add_n_monotone (m n : ℕ) : (m ≤ n) ↔ (m*(m+1) ≤ n*(n+1)) := by {
  apply Iff.intro
  intro h
  have h1 : (m+1) ≤ (n+1) := by
    exact Nat.add_le_add_right h 1
  exact Nat.mul_le_mul h h1
  intro h
  contrapose h
  simp at h
  simp
  have h1 : (n+1) < (m+1) := by
    exact Nat.add_lt_add_right h 1
  exact Nat.mul_lt_mul_of_lt_of_lt h h1
}

--wish had thought of this first and used eq_of_le for other
lemma n_sq_add_n_monotone_strict (m n : ℕ) : (m < n) ↔ (m*(m+1) < n*(n+1)) := by {
  apply Iff.intro
  intro h
  have h1 : (m+1) < (n+1) := by
    exact Nat.add_lt_add_right h 1
  exact Nat.mul_lt_mul_of_lt_of_lt h h1
  intro h
  contrapose h
  simp at h
  simp
  have h1 : (n+1) ≤ (m+1) := by
    exact Nat.add_le_add_right h 1
  exact (n_sq_add_n_monotone n m).mp h
}

lemma pred_legit (c : ℕ) : (c > 0) → (∃ a : ℕ, c = a+1) := by {
  intro h
  exact Nat.exists_eq_add_one.mpr h
}

lemma range_lem (b c : ℕ) : (c*(c+1) < b*(b+1) + 2*c) → (c ≤ b) := by {
  intro h
  have h0 : (c = 0) ∨ (c > 0) := by
    exact Nat.eq_zero_or_pos c
  rcases h0 with rfl | hn0
  · simp
  · apply pred_legit c at hn0
    rcases hn0 with ⟨a, rfl⟩
    have hba : (a + 1) * (a + 1 + 1) < b * (b + 1) + 2 * (a + 1) := h
    contrapose! hba
    have h_le : a + 1 > b := hba
    have h_le2 : a ≥ b := Nat.le_of_lt_succ h_le
    have h_mono : a * (a + 1) ≥ b * (b + 1) := (n_sq_add_n_monotone b a).mp h_le2
    calc b * (b + 1) + 2 * (a + 1)
      ≤ a * (a + 1) + 2 * (a + 1) := by linarith
      _ = (a + 1) * (a + 2) := by ring
}

lemma sum_range (a c : ℕ): (a*(a+1) ≤ 2*(∑ x ∈ Finset.range (c+1), x) ∧
  2*(∑ x ∈ Finset.range (c+1), x) < a*(a+1) + 2*c) → (a = c) := by {
    intro h
    have haltc : a ≤ c := by
      rw [infant_Gauss] at h
      have h1 : a*(a+1) ≤ c*(c+1) := by
        apply h.1
      apply (n_sq_add_n_monotone a c).mpr h1
    have hclta : c ≤ a := by
      refine range_lem a c ?_
      rw [infant_Gauss] at h
      exact h.2
    exact Nat.le_antisymm haltc hclta
  }

lemma sum_range_simp (a c : ℕ): (a ≤ c) ∧ (c*(c+1) < a*(a+1)+2*c) → a=c := by {
  intro h
  rcases h with ⟨h1, h2⟩
  rw [n_sq_add_n_monotone] at h1
  rw [← infant_Gauss c] at h1
  rw [← infant_Gauss] at h2
  rw [sum_range a c]
  exact And.symm ⟨h2, h1⟩
}

lemma lemma1 (a b c d : ℕ) : (a + b = c + d) ∧ (a ≤ c) → (b ≥ d) := by {
  intro h
  have h1 : a + b ≤ c + b := by
    exact Nat.add_le_add h.2 (Nat.le_refl b)
    --refine Nat.add_le_add ?h₁ ?h₂
    --exact h.2
    --exact Nat.le_refl b
  have h2 : c + d ≤ c + b := by
    rw [← h.1]
    exact h1
  exact Nat.le_of_add_le_add_left h2
}

--wondering about efficient handling of symmetry arguments
lemma lemma2 (a b c d : ℕ) : (a + b = c + d) ∧ (a ≥ c) → (b ≤ d) := by {
  intro h
  apply lemma1 c d a b
  rcases h with ⟨h1, h2⟩
  rw [h1]
  simp
  exact h2
}

--wish had thought of this one first
lemma lemma2_le (a b c d : ℕ) : (a + b ≤ c + d) ∧ (a ≥ c) → (b ≤ d) := by {
  intro h
  have h1 : a + b ≥ c + b := by
    apply Nat.add_le_add h.2 (Nat.le_refl b)
  have h2 : c + b ≤ c + d := by
    apply Nat.le_trans h1 h.1
  exact Nat.le_of_add_le_add_left h2
}

lemma lt_if_lt_add_right (a b c : ℕ) : a+c < b+c → a < b := by {
  intro h
  rw [Nat.add_lt_add_iff_right] at h
  exact h
}

theorem diag_fun_inj : diag_fun.Injective := by {
  unfold Function.Injective
  intros a b
  intro h
  unfold diag_fun at h
  apply mul_2_both_sides (∑ x ∈ Finset.range (a.1+a.2+1), x + a.2) (∑ x ∈ Finset.range (b.1+b.2+1), x + b.2) at h
  rw [Nat.mul_add, infant_Gauss] at h
  rw [Nat.mul_add 2 (∑ x ∈ Finset.range (b.1 + b.2 + 1), x) b.2, infant_Gauss (b.1+b.2)] at h
  --wish for WLOG
  have hab : ((a.1+a.2) ≥ (b.1+b.2) ∨ ((b.1+b.2) > (a.1+a.2))) := by
    exact le_or_gt (b.1 + b.2) (a.1 + a.2)
  rcases hab with ha | hb
  have ha2 :(a.1+a.2)*(a.1+a.2+1) ≥ (b.1+b.2)*(b.1+b.2+1) := by
    apply (n_sq_add_n_monotone (b.1+b.2) (a.1+a.2)).mp
    exact ha
  have ha3 : 2 * a.2 ≤ 2 * b.2 := by
    apply lemma2 ((a.1+a.2)*(a.1+a.2+1)) (2*a.2) ((b.1+b.2)*(b.1+b.2+1)) (2*b.2)
    apply And.intro ; exact h; exact ha2
  have hstar : 2*b.2 < 2*a.2 + 2*(a.1+a.2) ∨ a.1 = 0 := by
    have hbcases : b.1 = 0 ∨ b.1 > 0 := by
      exact Nat.eq_zero_or_pos b.1
    rcases hbcases with h0b | hnb
    · have hacases : a.2 = 0 ∨ a.2 > 0 := by
        exact Nat.eq_zero_or_pos a.2
      rcases hacases with h0a | hna
      · rw [h0a,h0b] at h
        simp at h
        rw [h0a]
        simp
        have hc : a.1 > 0 ∨ a.1 = 0 := by
          exact Or.symm (Nat.eq_zero_or_pos a.1)
        rcases hc with hcn | hc0
        · have hf2 : b.2*(b.2+1) < a.1*(a.1+1) ∨ b.2 = 0 := by
            rw [h]
            simp
            exact Or.symm (Nat.eq_zero_or_pos b.2)
          rcases hf2 with hf3 | hf4
          · rw [← n_sq_add_n_monotone_strict b.2 a.1] at hf3
            exact Or.inl hf3
          · apply Or.inl --learned "left" from LLMStep later
            rw [hf4]
            exact hcn
        · apply Or.inr
          exact hc0
      · rw [h0b] at ha
        simp at ha
        left
        have h5 : 2*b.2 ≤ 2*(a.1 + a.2) := by
          exact Nat.mul_le_mul_left 2 ha
        --LLMStep has only one suggestion here: linarith. but fails
        have h6 : 2*a.2 > 0 := by
          exact Nat.succ_mul_pos 1 hna
        exact lt_add_of_pos_of_le h6 h5
    · have h8 : b.2 < a.1 + a.2 := by
        have h9 : b.2 < b.2 + b.1 := by
          exact Nat.lt_add_of_pos_right hnb
        simp at ha
        --rw [add_comm] (not at h9) from LLMStep, apply? not helpful
        rw [add_comm] at h9
        exact Nat.lt_of_lt_of_le h9 ha
      have h10 : 2*b.2 < 2*(a.1 + a.2) := by
        refine Nat.mul_lt_mul_of_pos_left h8 ?hk
        simp
      left
      exact Nat.lt_add_left (2 * a.2) h10
  rcases hstar with han | ha0
  have hs2 : (b.1 + b.2) * ((b.1 + b.2) + 1) + 2 * b.2 < (b.1 + b.2) * ((b.1 + b.2) + 1) + (2 * a.2 + 2 * (a.1 + a.2)) := by
    exact Nat.add_lt_add_left han ((b.1 + b.2) * ((b.1 + b.2) + 1))
  rw [← h] at hs2
  have hs3 : (a.1 + a.2) * (a.1 + a.2 + 1) < (b.1 + b.2) * (b.1 + b.2 + 1) + (2 * (a.1 + a.2)) := by
    apply lt_if_lt_add_right ((a.1 + a.2) * (a.1 + a.2 + 1)) ((b.1 + b.2) * (b.1 + b.2 + 1) + 2 * (a.1 + a.2)) (2 * a.2)
    rw [add_comm (2 * a.2)  (2 * (a.1 + a.2))] at hs2
    have hlem : (b.1 + b.2) * (b.1 + b.2 + 1) + (2 * (a.1 + a.2) + 2 * a.2)
      = (b.1 + b.2) * (b.1 + b.2 + 1) + 2 * (a.1 + a.2) + 2 * a.2 := by
        exact Eq.symm (Nat.add_assoc ((b.1 + b.2) * (b.1 + b.2 + 1)) (2 * (a.1 + a.2)) (2 * a.2))
    rw [← hlem]
    exact hs2
  have hab : b.1 + b.2 = a.1 + a.2 := by
    apply sum_range_simp (b.1 + b.2) (a.1 + a.2)
    exact ⟨ha,hs3⟩
  rw [hab] at h
  simp at h
  rw [h] at hab
  simp at hab
  exact Prod.ext (id (Eq.symm hab)) h
  have hab : a.2 = b.1 + b.2 := by
    rw [ha0] at ha
    simp at ha
    simp at ha3
    have ha4 : a.2 ≤ b.1 + b.2 := by
      exact le_add_of_le_right ha3
    exact Nat.le_antisymm ha4 ha
  rw [← hab] at h
  rw [ha0] at h
  simp at h
  have hb0 : b.1 = 0 := by
    rw [h] at hab
    exact Nat.add_eq_right.mp (Eq.symm hab)
  have hab0 : a.1 = b.1 := by
    rw [ha0]
    rw [hb0]
  exact Prod.ext hab0 h
  --now symmetric argument or shortcut
  have hstar2 : 2*a.2 < 2*b.2 + 2*(b.1+b.2) := by
    have h2 : a.2 ≤ a.1 + a.2 := by
      exact Nat.le_add_left a.2 a.1
    have h3 : a.2 < b.1 + b.2 := by
      exact Nat.lt_of_le_of_lt h2 hb
    have h4 : 2 * a.2 < 2 * (b.1 + b.2) := by
      refine Nat.mul_lt_mul_of_pos_left h3 ?hk
    exact Nat.lt_add_left (2 * b.2) h4
  have ht2 : (a.1 + a.2) * ((a.1 + a.2) + 1) + 2 * a.2 < (a.1 + a.2) * ((a.1 + a.2) + 1) + (2 * b.2 + 2 * (b.1 + b.2)) := by
    exact Nat.add_lt_add_left hstar2 ((a.1 + a.2) * ((a.1 + a.2) + 1))
  rw [h] at ht2
  --used copy and paste, find and replace a,b for ht3 from hs3
  have ht3 : (b.1 + b.2) * (b.1 + b.2 + 1) < (a.1 + a.2) * (a.1 + a.2 + 1) + (2 * (b.1 + b.2)) := by
    apply lt_if_lt_add_right ((b.1 + b.2) * (b.1 + b.2 + 1)) ((a.1 + a.2) * (a.1 + a.2 + 1) + 2 * (b.1 + b.2)) (2 * b.2)
    rw [add_comm (2 * b.2)  (2 * (b.1 + b.2))] at ht2
    have hlem : (a.1 + a.2) * (a.1 + a.2 + 1) + (2 * (b.1 + b.2) + 2 * b.2)
      = (a.1 + a.2) * (a.1 + a.2 + 1) + 2 * (b.1 + b.2) + 2 * b.2 := by
        exact Eq.symm (Nat.add_assoc ((a.1 + a.2) * (a.1 + a.2 + 1)) (2 * (b.1 + b.2)) (2 * b.2))
    rw [← hlem]
    exact ht2
  have hb2 : a.1 + a.2 ≤ b.1 + b.2 := by
    exact Nat.le_of_succ_le hb
  have hab : a.1 + a.2 = b.1 + b.2 := by
    apply sum_range_simp (a.1 + a.2) (b.1 + b.2)
    exact ⟨hb2,ht3⟩
  rw [hab] at h
  simp at h
  rw [h] at hab
  simp at hab
  exact Prod.ext (id (hab)) h
}

variable (C : Set (ℕ × ℕ))

theorem nat_prod_countable : Set.Countable C := by {
  apply (Set.countable_iff_exists_injOn).mpr
  use diag_fun
  apply Set.injOn_of_injective
  exact diag_fun_inj
}

lemma diag_fun_inj_explicit (a b : ℕ × ℕ) : (diag_fun a = diag_fun b) → (a = b) := by {
  intro h
  have h2 : diag_fun.Injective := by
    exact diag_fun_inj
  unfold Function.Injective at h2
  apply h2
  exact h
}

lemma proj_fst (a b : ℕ × ℕ) : (a = b) → (a.1 = b.1) := by {
  intro h
  exact congrArg Prod.fst h
}

lemma proj_snd (a b : ℕ × ℕ) : (a = b) → (a.2 = b.2) := by {
  intro h
  exact congrArg Prod.snd h
}

def diag3_fun (a : (ℕ × ℕ × ℕ)) : ℕ := diag_fun ((diag_fun (a.2.1,a.2.2)),a.1)

theorem diag3_fun_inj : diag3_fun.Injective := by {
  unfold Function.Injective
  intros a b
  intro h
  unfold diag3_fun at h
  have h1 : (diag_fun (a.2.1,a.2.2) , a.1) = (diag_fun (b.2.1,b.2.2) , b.1) := by
    exact diag_fun_inj_explicit (diag_fun (a.2.1, a.2.2), a.1) (diag_fun (b.2.1, b.2.2), b.1) h
  have h2 : a.1 = b.1 := by
    exact (proj_snd (diag_fun (a.2.1,a.2.2) , a.1) (diag_fun (b.2.1,b.2.2) , b.1) h1)
  have h3 : diag_fun (a.2.1,a.2.2) = diag_fun (b.2.1,b.2.2) := by
    exact (proj_fst (diag_fun (a.2.1,a.2.2) , a.1) (diag_fun (b.2.1,b.2.2) , b.1) h1)
  have h4 : a.2 = b.2 := by
    exact diag_fun_inj_explicit _ _ h3
  exact Prod.ext h2 h4
}

variable (D : Set (ℕ × ℕ × ℕ))

theorem nat_trip_prod_countable : Set.Countable D := by {
  apply (Set.countable_iff_exists_injOn).mpr
  use diag3_fun
  apply Set.injOn_of_injective
  exact diag3_fun_inj
}

def rat_fun (q : ℚ) : ℕ := diag_fun (spread_fun q.num, q.den)

theorem rat_fun_inj : rat_fun.Injective := by {
  unfold Function.Injective
  intros a b
  intro h
  unfold rat_fun at h
  have h1 : (spread_fun a.num, a.den) = (spread_fun b.num, b.den) := by
    exact diag_fun_inj_explicit _ _ h
  have h2 : a.den = b.den := by
    exact proj_snd _ _ h1
  have h3 : spread_fun a.num = spread_fun b.num := by
    exact proj_fst _ _ h1
  have h4 : a.num = b.num := by
    exact spread_fun_inj_explicit _ _ h3
  exact Rat.ext h4 h2
}

lemma rat_fun_inj_explicit (a b : ℚ) : (rat_fun a = rat_fun b) → (a = b) := by {
  intro h
  have h2 : rat_fun.Injective := by
    exact rat_fun_inj
  unfold Function.Injective at h2
  apply h2
  exact h
}

variable (A : Set ℚ)

theorem rat_countable : Set.Countable A := by {
  apply (Set.countable_iff_exists_injOn).mpr
  use rat_fun
  apply Set.injOn_of_injective
  exact rat_fun_inj
}

def rat_prod_fun (s : (ℚ × ℚ)) : ℕ := diag_fun (rat_fun s.1, rat_fun s.2)

theorem rat_prod_fun_inj : rat_prod_fun.Injective := by {
  unfold Function.Injective
  intros a b
  intro h
  unfold rat_prod_fun at h
  have h1 : (rat_fun a.1, rat_fun a.2) = (rat_fun b.1, rat_fun b.2) := by
    exact diag_fun_inj_explicit _ _ h
  have h2 : rat_fun a.2 = rat_fun b.2 := by
    exact proj_snd _ _ h1
  have h3 : rat_fun a.1 = rat_fun b.1  := by
    exact proj_fst _ _ h1
  have h4 : a.2 = b.2 := by
    exact rat_fun_inj_explicit _ _ h2
  have h5 : a.1 = b.1 := by
    exact rat_fun_inj_explicit _ _ h3
  exact Prod.ext h5 h4
}

variable (E : Set (ℚ × ℚ))

theorem rat_prod_countable : Set.Countable E := by {
  apply (Set.countable_iff_exists_injOn).mpr
  use rat_prod_fun
  apply Set.injOn_of_injective
  exact rat_prod_fun_inj
}

variable (a b c : (ℝ × ℝ))

noncomputable def euclideanNorm (x : (ℝ × ℝ)) : ℝ :=
  Real.sqrt (x.1^2 + x.2^2)

noncomputable def euclideanDist (x y : (ℝ × ℝ)) : ℝ :=
  euclideanNorm (x-y)

def myPoint1 : (ℝ × ℝ) :=
  ⟨ 3 , 5 ⟩

noncomputable def myPoint2 : (ℝ × ℝ) :=
  ⟨ Real.sqrt 3, 4 ⟩

def myPoint3 : (ℝ × ℝ) :=
  ⟨ -1.4, 4⟩

#eval myPoint1

#eval (dist myPoint1 myPoint3 : ℝ)

#check (euclideanDist myPoint1 myPoint3)
