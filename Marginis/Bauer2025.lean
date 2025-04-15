import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!

## Spreen spaces and the synthetic Kreisel-Lacombe-Shoenfield-Tseitin theorem
Andrej Bauer

Code by ChatGPT, mostly.
-/


-- The Rosolini dominance Σ: a set of truth values
def rosolini_sigma : Set Bool :=
  { p | ∃ f : ℕ → Bool, p = true ↔ ∃ n, f n = true }

-- Theorem: every Boolean is in rosolini_sigma
theorem rosolini_sigma_univ : rosolini_sigma = Set.univ := by
  ext p
  unfold rosolini_sigma
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  cases p
  case false =>
    -- Define f to be constantly false
    use λ _ => false
    simp
  case true =>
    -- Define f to be true at 0
    use λ n => n = 0
    simp
