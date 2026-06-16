module
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Set.Finite.Basic
import Mathlib
/-!

## Localic completion of generalized metric spaces II: Powerlocales

[STEVEN VICKERS](http://logicandanalysis.org/index.php/jla/article/view/34)

The finite powerset of a set.
We show that in the presence of a `Fintype` it is the same as the ordinary powerset,
and in the case of `ℕ, ℚ, ℝ, ℂ` it is not the same.

-/


def setSetFin X := { A : Set X | Set.Finite A}

-- The ordinary powerset can be defined in these two, identical, ways:
def setSetUniv X := (Set.univ : Set (Set X))
def powersetUniv X := 𝒫 (Set.univ : Set X)

example (X) : setSetUniv X = powersetUniv X := by
  unfold setSetUniv powersetUniv
  simp only [Set.powerset_univ]

example (X) [Fintype X] : setSetFin X = setSetUniv X := by
  ext x
  constructor
  . intro; trivial
  . intro; exact Set.toFinite x

/-- The finite powerset of an infinite set `X` is distinct from the powerset of `X`. -/
lemma finite_powerset_improper [Infinite X]: setSetFin X ≠ setSetUniv X := by
  intro hc
  have h₀: ∀ S, S ∈ setSetFin X ↔ S ∈ setSetUniv X := by
    unfold setSetFin setSetUniv at *
    simp_all
  have h₁: Set.univ ∈ setSetUniv X := by unfold setSetUniv; simp
  have h₂: Set.univ ∈ setSetFin X := by rw [h₀];exact h₁
  have := Set.finite_univ_iff.mp h₂
  exact not_finite X

example : setSetFin ℕ ≠ setSetUniv ℕ := finite_powerset_improper
example : setSetFin ℤ ≠ setSetUniv ℤ := finite_powerset_improper
example : setSetFin ℚ ≠ setSetUniv ℚ := finite_powerset_improper

/-- There are infinitely many real numbers. -/
instance : Infinite ℝ := Infinite.of_injective (λ x : ℕ ↦ x)
  fun _ _ => Nat.cast_inj.mp

/-- There are infinitely many complex numbers. -/
instance : Infinite ℂ := Infinite.of_injective (λ x : ℝ ↦ x)
  fun _ _ => Complex.ofReal_inj.mp

example : setSetFin ℝ ≠ setSetUniv ℝ := finite_powerset_improper

example : setSetFin ℂ ≠ setSetUniv ℂ := finite_powerset_improper
