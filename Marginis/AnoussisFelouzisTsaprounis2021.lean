import Mathlib.Order.Cofinal
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.FixedPoint
import Mathlib.SetTheory.Cardinal.Regular
/-!

# Almost disjoint families and ultrapowers

[MICHALIS ANOUSSIS, VAGGELIS FELOUZIS, and KONSTANTINOS TSAPROUNIS](http://logicandanalysis.org/index.php/jla/article/view/398)

discusses regular cardinals. Here we prove that no natural nunmber is regular.
-/

theorem not_regular_nat {n : ℕ} : ¬ Cardinal.IsRegular n := by
  intro h
  have h₀ : Cardinal.aleph0 ≤ n := Cardinal.IsRegular.aleph0_le h
  have h₁ : (n : Cardinal.{u_1}) < Cardinal.aleph0 := by
    refine Cardinal.lt_aleph0.mpr ?_
    use n
  have h₂ : (n : Cardinal.{u_1}) < (n : Cardinal.{u_1}) :=  Cardinal.IsRegular.nat_lt h n
  aesop
