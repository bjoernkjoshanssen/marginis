import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!

## A point-free look at Ostrowski's theorem and absolute values
Ming Ng, Steven Vickers

Code by ChatGPT, mostly.
-/

/-- From Convention 1.7. -/
lemma convention_1_7 : ∀ x y : ℝ, x ≥ y ↔ ∀ q : ℚ, x < q → y < q := by
  intros x y
  constructor
  · -- → direction: if x ≥ y, then any q > x is also > y
    intros hxy q hxq
    linarith
  · -- ← direction: contrapose the implication
    contrapose!
    intro hxy -- x < y
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hxy
    use q
    constructor
    · exact hq₁ -- x < q
    · exact le_of_lt hq₂
