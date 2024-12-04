import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Data.Real.Basic

/-!

## Infinite-Dimensional Linear Algebra and Solvability of Partial Differential Equations
by TODOR D. TODOROV

We prove some elementary versions of the statement that
the standard basis of `ℝ³` is linearly independent.
-/

lemma indep₀ (c₀ c₁ c₂ : ℝ) :
c₀ • ![(1:ℝ),0,0] + c₁ • ![0,1,0] + c₂ • ![0,0,1] = ![c₀,c₁,c₂] := by aesop

lemma indep₁ (c₀ c₁ c₂ : ℝ)
(h : c₀ • ![(1:ℝ),0,0] + c₁ • ![0,1,0] + c₂ • ![0,0,1] = 0) : c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  aesop

lemma indep₂ (c : Fin 3 → ℝ)
(h : c 0 • ![(1:ℝ),0,0] + c 1 • ![0,1,0] + c 2 • ![0,0,1] = 0) : c = 0 := by
  simp at h
  ext i
  fin_cases i <;> aesop

lemma indep₃ (c : Fin 3 → ℝ)
(h : c 0 • Function.update (0 : Fin 3 → ℝ) 0 1
   + c 1 • Function.update (0 : Fin 3 → ℝ) 1 1
   + c 2 • Function.update (0 : Fin 3 → ℝ) 2 1 = 0) : c = 0 := by
  have : Function.update (0 : Fin 3 → ℝ) 0 1 = ![1,0,0] := by
    ext i;fin_cases i <;> aesop
  rw [this] at h
  have : Function.update (0 : Fin 3 → ℝ) 1 1 = ![0,1,0] := by
    ext i;fin_cases i <;> aesop
  rw [this] at h
  have : Function.update (0 : Fin 3 → ℝ) 2 1 = ![0,0,1] := by
    ext i;fin_cases i <;> aesop
  rw [this] at h
  exact indep₂ c h