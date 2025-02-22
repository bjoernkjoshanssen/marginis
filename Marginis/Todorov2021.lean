import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Fin.Tuple
import Mathlib.Tactic.FinCases

/-!

## Infinite-Dimensional Linear Algebra and Solvability of Partial Differential Equations

[TODOR D. TODOROV](http://logicandanalysis.org/index.php/jla/article/view/376)

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
(h : c 0 • @Pi.single (Fin 3) (fun _ => ℝ) _ _ 0 1
   + c 1 • @Pi.single (Fin 3) (fun _ => ℝ) _ _ 1 1
   + c 2 • @Pi.single (Fin 3) (fun _ => ℝ) _ _ 2 1 = 0) : c = 0 := by
  have := @Pi.single (Fin 3) (fun _ => ℝ) _ _ 0 1
  have : @Pi.single (Fin 3) (fun _ => ℝ) _ _ 0 1 = ![1,0,0] := by
    ext i;fin_cases i <;> aesop
  rw [this] at h
  have : @Pi.single (Fin 3) (fun _ => ℝ) _ _ 1 1 = ![0,1,0] := by
    ext i;fin_cases i <;> aesop
  rw [this] at h
  have : @Pi.single (Fin 3) (fun _ => ℝ) _ _ 2 1 = ![0,0,1] := by
    ext i;fin_cases i <;> aesop
  rw [this] at h
  exact indep₂ c h
