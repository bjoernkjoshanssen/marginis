import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.RingTheory.Regular.RegularSequence


/-!
# First order irrationality criteria for series
by LEE A. BUTLER

Corollary 2.2 in the paper is inspired by some work of `Viggo Brun`.
It is mentioned that Corollary 2.2 applies to the sequence qₙ below.
We verify that fact in `corollary_2_2_example` below.
In fact, the assumption `n ≥ 1` is not needed.
-/

def q : ℕ → ℕ := λ n ↦ 2^(2^n)

lemma all_positive (n:ℕ) : 0 < q n := by
  unfold q
  simp

lemma quad (a : ℕ) (h : 2 ≤ a) : a^2 - a + 1 < a^2 := by
  suffices a^2 - a + 1 - 1 < a^2 - 1 by
    exact Nat.add_lt_of_lt_sub this
  simp
  suffices 1 < a by
    refine Nat.sub_lt_sub_left ?_ h
    exact Nat.sqrt_lt'.mp h
  exact h

theorem corollary_2_2_example (n : ℕ) : q (n+1) > (q n)^2 - q n + 1 := by
  unfold q
  have : 2^(2^(n+1)) = (2^(2^n))^2 := by ring_nf
  rw [this]
  simp
  apply quad
  have : 2 = 2^(2^0) := by decide
  nth_rewrite 1 [this]
  have : 2^0 ≤ 2^n := by
    refine Nat.pow_le_pow_of_le_right ?hx ?_
    decide
    exact Nat.zero_le n
  refine Nat.pow_le_pow_of_le_right ?hx ?_
  tauto
