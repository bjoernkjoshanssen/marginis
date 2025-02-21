import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.Separation

/-!

# Description of locally finite families from a nonstandard point of view

[ULF LEONARD CLOTZ](http://logicandanalysis.org/index.php/jla/article/view/42)

studies the neighbourhood-monads of the standard points.
Here we look at neighborhood filter in Lean and prove uniqueness of
limits.
-/

example (f : ℝ → ℝ) (a L₀ L₁ : ℝ)
  (h₀ : Filter.Tendsto f (nhds a) (nhds L₀))
  (h₁ : Filter.Tendsto f (nhds a) (nhds L₁)) : L₀ = L₁  := by
  exact @tendsto_nhds_unique ℝ ℝ _ _ f (nhds a) L₀ L₁ _ h₀ h₁
