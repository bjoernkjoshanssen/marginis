import Mathlib.Data.Real.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!

## A density version of a theorem of Banach
David A. Ross

Code by ChatGPT, mostly.
-/


open Filter Real Set

-- Define the counting function: how many elements of I are ≤ n
def count_le (I : ℕ → Prop) [DecidablePred I] (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (λ k => I k) |>.card

-- Define the density function sequence: a(n)/n
noncomputable def density_seq (I : ℕ → Prop) [DecidablePred I] (n : ℕ) : ℝ :=
  (count_le I n : ℝ) / (n + 1)

-- Define the upper asymptotic density as the limsup of that sequence
noncomputable def upper_density (I : ℕ → Prop) [DecidablePred I] : ℝ :=
  limsup  (density_seq I) atTop
