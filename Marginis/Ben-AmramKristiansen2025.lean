import Mathlib.Data.Real.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!

## A degree structure on representations of irrational numbers
Amir Ben-Amram, Lars Kristiansen

Code by ChatGPT, mostly.
-/

-- The Dedekind cut representation of a real number α as a function from ℚ → {0, 1}
noncomputable def dedekind_cut_fn (α : ℝ) : ℚ → ℕ :=
  λ q => if (q : ℝ) < α then 0 else 1
