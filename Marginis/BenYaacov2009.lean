module
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
/-!

## Modular functionals and perturbations of Nakano spaces

[ITAI BEN-YAACOV](http://logicandanalysis.org/index.php/jla/article/view/11)

defines L₀(X,𝓑,μ) to be the space of measurable functions
f:X→ℝ up to a.e. equality.

Here we define that and give an example.

Note that the Lp seminorm `MeasureTheory.eLpNorm` is equal to 0 for p=0.

-/
noncomputable section

def L₀ {X : Type*} { _ : MeasureTheory.MeasureSpace X} :=
  @MeasureTheory.Lp X ℝ
  MeasureTheory.MeasureSpace.toMeasurableSpace _ 0 MeasureTheory.volume

def constant_ae (c : NNReal): ℝ →ₘ[MeasureTheory.volume] ℝ := MeasureTheory.AEEqFun.mk (fun _ ↦ c) MeasureTheory.aestronglyMeasurable_const

def c₀ := constant_ae 0

def c₁ := constant_ae 1

/-- The constant 0 function on `ℝ` is in L₀. -/
example : @L₀ ℝ Real.measureSpace := ⟨c₀, (QuotientAddGroup.eq_zero_iff (c₀)).mp rfl⟩


/-- The constant 0 function on any `X` is in L₀. -/
example {X : Type*} { m : MeasureTheory.MeasureSpace X} : @L₀ X m := ⟨
  @MeasureTheory.AEEqFun.mk X _
    MeasureTheory.volume ℝ _ (fun _ => 0)
    (MeasureTheory.aestronglyMeasurable_const),
    (QuotientAddGroup.eq_zero_iff
          (MeasureTheory.AEEqFun.mk (fun _ ↦ 0) MeasureTheory.aestronglyMeasurable_const)).mp
      rfl⟩

example {X : Type*} { m : MeasureTheory.MeasureSpace X} : @L₀ X m :=
  ⟨
  @MeasureTheory.AEEqFun.mk X _
    MeasureTheory.volume ℝ _ (fun _ => 1)
    (MeasureTheory.aestronglyMeasurable_const),
    by
      refine MeasureTheory.Lp.mem_Lp_iff_eLpNorm_lt_top.mpr ?_
      unfold MeasureTheory.eLpNorm
      simp only [↓reduceIte, ENNReal.zero_lt_top]
    ⟩
