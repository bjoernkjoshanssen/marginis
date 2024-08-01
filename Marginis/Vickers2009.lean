
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


def F_Vickers X := { A : Set X | Set.Finite A}

-- The ordinary powerset can be defined in these two, identical, ways:
def P_Vickers X := (Set.univ : Set (Set X))
def P' X := 𝒫 (Set.univ : Set X)

example : P_Vickers X = P' X := by
  unfold P_Vickers P'
  simp only [Set.setOf_true, Set.powerset_univ]

example [Fintype X] : F_Vickers X = P_Vickers X := by
  ext x
  constructor
  . intro; trivial
  . intro; exact Set.toFinite x

lemma finite_powerset_improper [Infinite X]: F_Vickers X ≠ P_Vickers X := by
  intro hc
  have h₀: ∀ S, S ∈ F_Vickers X ↔ S ∈ P_Vickers X := fun S ↦ Eq.to_iff (congrArg (Membership.mem S) hc)
  have h₁: Set.univ ∈ P_Vickers X := by unfold P_Vickers; simp
  have h₂: Set.univ ∈ F_Vickers X := by rw [h₀];exact h₁
  have h₃: Finite X := Set.finite_univ_iff.mp h₂
  exact not_finite X

example : F_Vickers ℕ ≠ P_Vickers ℕ := finite_powerset_improper
example : F_Vickers ℤ ≠ P_Vickers ℤ := finite_powerset_improper
example : F_Vickers ℚ ≠ P_Vickers ℚ := finite_powerset_improper

instance : Infinite ℝ := by
  exact @Infinite.of_injective ℝ ℕ _ (λ x ↦ x) (by
    intro x y h
    simp only [Nat.cast_inj] at h
    exact h
  )

example : F_Vickers ℝ ≠ P_Vickers ℝ := finite_powerset_improper

instance : Infinite ℂ := by
  exact @Infinite.of_injective ℂ ℝ _ (λ x ↦ x) (by
    intro x y h
    exact Complex.ofReal_inj.mp h
  )

example : F_Vickers ℂ ≠ P_Vickers ℂ := finite_powerset_improper
