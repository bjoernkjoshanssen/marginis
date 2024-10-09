import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.RingTheory.Regular.RegularSequence

/-!
## Genericity and UD–random reals
by
# WESLEY CALVERT, JOHANNA N.Y. FRANKLIN.

This concerns the second sentence in the Introduction in the paper.

We define uniform distribution and prove that the constant 0 sequence is not uniformly distributed.
-/

open Finset

/-- The triple (a,b,ε) satisfies the conditions for uniform distribution of x. -/
def uniformly_distributed_at (x : ℕ → Set.Ico (0:ℝ) 1) (a b ε : ℝ) :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    abs (card (filter (λ i : Fin n ↦ a < x i ∧ x i < b) univ) - (b - a) * n) < n * ε

/-- The sequence `x` is uniformly distributed in the half-open unit interval. -/
def uniformly_distributed (x : ℕ → Set.Ico (0:ℝ) 1) :=
  ∀ a b ε : ℝ, 0 ≤ a → a < b → b ≤ 1 → ε > 0 → uniformly_distributed_at x a b ε

/-- The constant zero sequence is not uniformly distributed. -/
lemma zero_not_uniformly_distributed : ¬ uniformly_distributed (λ _ ↦ ⟨0,by simp⟩) := by
  unfold uniformly_distributed uniformly_distributed_at
  push_neg
  use (1:ℝ)/2;use (1:ℝ);use (1:ℝ)/2
  constructor;aesop;constructor;exact one_half_lt_one
  constructor;rfl;constructor;aesop
  intro n₀;use n₀
  constructor;rfl;simp
  split_ifs with h
  . exfalso;contrapose h;simp
  . simp;ring_nf;apply @le_abs_self ℝ
