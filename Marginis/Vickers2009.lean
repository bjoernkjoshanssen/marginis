
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Denumerable

/-

The finite powerset of a set.
We show that in the presence of a `Fintype` it is the same as the ordinary powerset,
and in the case of `ℕ, ℚ, ℝ, ℂ` it is not the same.

Inspired by:

Localic completion of generalized metric spaces II: Powerlocales
STEVEN VICKERS
-/

def F X := { A : Set X | Set.Finite A}

-- The ordinary powerset can be defined in these two, identical, ways:
def P X := (Set.univ : Set (Set X))
def P' X := 𝒫 (Set.univ : Set X)

example : P X = P' X := by
  unfold P P'
  simp only [Set.setOf_true, Set.powerset_univ]

example [Fintype X] : F X = P X := by
  ext x
  constructor
  . intro; trivial
  . intro; exact Set.toFinite x

lemma l₁ [Infinite X]: F X ≠ P X := by
  intro hc
  have h₀: ∀ S, S ∈ F X ↔ S ∈ P X := fun S ↦ Eq.to_iff (congrArg (Membership.mem S) hc)
  have h₁: Set.univ ∈ P X := by unfold P; simp
  have h₂: Set.univ ∈ F X := by rw [h₀];exact h₁
  have h₃: Finite X := Set.finite_univ_iff.mp h₂
  exact not_finite X

example : F ℕ ≠ P ℕ := l₁
example : F ℤ ≠ P ℤ := l₁
example : F ℚ ≠ P ℚ := l₁

instance : Infinite ℝ := by
  exact @Infinite.of_injective ℝ ℕ _ (λ x ↦ x) (by
    intro x y h
    simp only [Nat.cast_inj] at h
    exact h
  )

example : F ℝ ≠ P ℝ := l₁

instance : Infinite ℂ := by
  exact @Infinite.of_injective ℂ ℝ _ (λ x ↦ x) (by
    intro x y h
    exact Complex.ofReal_inj.mp h
  )

example : F ℂ ≠ P ℂ := l₁
