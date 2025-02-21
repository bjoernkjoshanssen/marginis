import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

/-!

# Covering entropy for types in tracial W^*- algebras

[DAVID JEKEL](http://logicandanalysis.org/index.php/jla/article/view/468)

The first displayed equation in the paper
includes the term
`τ (X₁ * Y * X₂ * Z) ^ 2`
Here τ is the trace and * is matrix multiplication.
There are two ways to parenthesize this and here we prove their inequivalence.
Perhaps it does not matter for the paper, however.
In that sense, mathematical articles may be underdetermined without being wrong.

We give examples over ℚ, ℝ, ℂ. Over each we can use the tactic `aesop`;
over ℚ we can also use `decide`.
-/

section Real
def I : Fin 2 → Fin 2 → ℝ := (λ x y ↦ ite (x=y) 1 0) -- = !![ 1,0;0,1]
lemma square : I^2 = I := by unfold I; aesop;

def τ : (Fin 2 → Fin 2 → ℝ) → ℝ := Matrix.trace
lemma two : τ I = 2 := by unfold τ I Matrix.trace; simp

lemma parentheses_matter : (τ I)^2 ≠ τ (I^2) := by
  rw [square,two];ring_nf;simp

/-- Lean's convention is perhaps surprising here: -/
lemma without_parentheses : τ (I)^2 = (τ I)^2 := rfl
end Real

section Rational
  def Iℚ : Fin 2 → Fin 2 → ℚ := (λ x y ↦ ite (x=y) 1 0) -- = !![ 1,0;0,1]
  lemma squareℚ : Iℚ^2 = Iℚ := by unfold Iℚ; decide;

  def τℚ : (Fin 2 → Fin 2 → ℚ) → ℚ := Matrix.trace
  lemma twoℚ : τℚ Iℚ = 2 := by unfold τℚ Iℚ Matrix.trace; simp

  lemma parentheses_matterℚ : (τℚ Iℚ)^2 ≠ τℚ (Iℚ^2) := by
    rw [squareℚ,twoℚ];ring_nf;simp

  lemma without_parenthesesℚ : τℚ (Iℚ)^2 = (τℚ Iℚ)^2 := rfl
end Rational

section Complex
  def Iℂ : Fin 2 → Fin 2 → ℂ := (λ x y ↦ ite (x=y) 1 0) -- = !![ 1,0;0,1]
  lemma squareℂ : Iℂ^2 = Iℂ := by unfold Iℂ; aesop;

  def τℂ : (Fin 2 → Fin 2 → ℂ) → ℂ := Matrix.trace
  lemma twoℂ : τℂ Iℂ = 2 := by unfold τℂ Iℂ Matrix.trace; simp

  lemma parentheses_matterℂ : (τℂ Iℂ)^2 ≠ τℂ (Iℂ^2) := by
    rw [squareℂ,twoℂ];ring_nf;simp

  lemma without_parenthesesℂ : τℂ (Iℂ)^2 = (τℂ Iℂ)^2 := rfl
end Complex
