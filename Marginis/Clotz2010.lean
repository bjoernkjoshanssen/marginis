import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

/-
Description of locally finite families from a nonstandard
point of view
ULF LEONARD CLOTZ

studies the neighbourhood-monads of the standard points.
Here we look at neighborhood filter in Lean and prove uniqueness of
limits.
-/

lemma start {f : ℝ → ℝ} {a L₀ L₁ : ℝ}
  (h₀ : Filter.Tendsto f (nhds a) (nhds L₀))
  (h₁ : Filter.Tendsto f (nhds a) (nhds L₁)) : ¬ L₀ < L₁  := by
  intro hc
  have hi₀: Set.Ioo (L₀ - |L₀-L₁|/2) (L₀ + |L₀-L₁|/2) ∈ nhds L₀ := by
    apply Ioo_mem_nhds
    simp;contrapose hc;simp at *;linarith
    simp;contrapose hc;simp at *;linarith
  have hi₁: Set.Ioo (L₁ - |L₀-L₁|/2) (L₁ + |L₀-L₁|/2) ∈ nhds L₁ := by
    apply Ioo_mem_nhds
    simp;contrapose hc;simp at *;linarith
    simp;contrapose hc;simp at *;linarith
  have : (Set.Ioo (L₀ - |L₀-L₁|/2) (L₀ + |L₀-L₁|/2))
        ∩ Set.Ioo (L₁ - |L₀-L₁|/2) (L₁ + |L₀-L₁|/2) = ∅ := by
    ext x
    constructor
    · intro hx₀
      simp at hx₀
      · contrapose hx₀
        simp
        intro _ h₁ h₂
        exfalso
        have h₃: L₁ - |L₀ - L₁| / 2
          < L₀ + |L₀ - L₁| / 2 := gt_trans h₁ h₂
        simp at h₃
        contrapose h₃
        simp
        ring_nf
        suffices L₀ + |L₀ - L₁| = L₁ by linarith
        have : |L₀ - L₁| = |L₁ - L₀| := abs_sub_comm L₀ L₁
        rw [this]
        have : |L₁ - L₀| = L₁ - L₀ := (@abs_eq_self ℝ _ (L₁-L₀)).mpr (by
            suffices L₀ ≤ L₁ by
              exact sub_nonneg_of_le this
            exact le_of_lt hc
          )
        rw [this]
        simp
    tauto
  have : ∅ ∈ Filter.map f (nhds a) := by
    rw [← this]
    exact Filter.inter_mem (h₀ hi₀) (h₁ hi₁)
  simp at this

example (f : ℝ → ℝ) (a L₀ L₁ : ℝ)
  (h₀ : Filter.Tendsto f (nhds a) (nhds L₀))
  (h₁ : Filter.Tendsto f (nhds a) (nhds L₁)) : L₀ = L₁  := by
  have g₀ : ¬ L₀ < L₁ := start h₀ h₁
  have g₁ : ¬ L₁ < L₀ := start h₁ h₀
  linarith
