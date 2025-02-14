import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.LpSpace

/-!

## Modular functionals and perturbations of Nakano spaces
by ITAI BEN-YAACOV

defines L₀(X,𝓑,μ) to be the space of measurable functions
f:X→ℝ up to a.e. equality.

Here we define that and give an example.
-/

def L₀ {X : Type*} { _ : MeasureTheory.MeasureSpace X} :=
  @MeasureTheory.Lp X ℝ
  MeasureTheory.MeasureSpace.toMeasurableSpace _ 0 MeasureTheory.volume

/-- The constant 0 function on `ℝ` is in L₀. -/
example : @L₀ ℝ Real.measureSpace := ⟨
  @MeasureTheory.AEEqFun.mk ℝ _
    MeasureTheory.volume ℝ _ (fun _ => 0)
    (MeasureTheory.aestronglyMeasurable_const),
    (QuotientAddGroup.eq_zero_iff
          (MeasureTheory.AEEqFun.mk (fun _ ↦ 0) MeasureTheory.aestronglyMeasurable_const)).mp
      rfl⟩

/-- The constant 0 function on any `X` is in L₀. -/
example {X : Type*} { m : MeasureTheory.MeasureSpace X} : @L₀ X m := ⟨
  @MeasureTheory.AEEqFun.mk X _
    MeasureTheory.volume ℝ _ (fun _ => 0)
    (MeasureTheory.aestronglyMeasurable_const),
    (QuotientAddGroup.eq_zero_iff
          (MeasureTheory.AEEqFun.mk (fun _ ↦ 0) MeasureTheory.aestronglyMeasurable_const)).mp
      rfl⟩
