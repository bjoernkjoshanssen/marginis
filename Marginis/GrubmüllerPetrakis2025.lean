import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!

## A predicative approach to the constructive integration theory of locally compact metric spaces
Fabian Lukas Grubmüller, Iosif Petrakis

Code by ChatGPT, partly.
-/


-- Assume A and B are disjoint sets of type α
def chi {α : Type*} (A B : Set α)
  [DecidablePred fun x : (A ∪ B : Set α) => x.1 ∈ A] : (A ∪ B : Set α) → Bool :=
  λ x => if x.1 ∈ A then true else false
