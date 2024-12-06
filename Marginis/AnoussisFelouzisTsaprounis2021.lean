import Mathlib.SetTheory.Cardinal.Cofinality
/-!

# Almost disjoint families and ultrapowers
by MICHALIS ANOUSSIS
VAGGELIS FELOUZIS
KONSTANTINOS TSAPROUNIS

discusses regular cardinals. Here we prove that no natural nunmber is regular.
-/

theorem not_regular_nat {n : ℕ} : ¬ Cardinal.IsRegular n := by
  intro h
  have h₀ : Cardinal.aleph0 ≤ n := Cardinal.IsRegular.aleph0_le h
  have h₁ : (n : Cardinal.{u_1}) < Cardinal.aleph0 := by
    refine Cardinal.lt_aleph0.mpr ?_
    use n
  have h₂ : (n : Cardinal.{u_1}) < (n : Cardinal.{u_1}) := gt_of_ge_of_gt h₀ h₁
  aesop
