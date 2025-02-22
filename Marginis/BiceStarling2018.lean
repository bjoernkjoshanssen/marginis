import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Clopen

/-!

# Locally compact Stone duality

[Tristan Bice and Charles Starling](http://logicandanalysis.org/index.php/jla/article/view/287)

It is proved that "Compact clopen pseudobasic posets are characterized by separativity."

As a first formal step in that direction we prove some basic results about clopen sets.

-/

example {α : Type} [TopologicalSpace α] : IsClopen (Set.univ : Set α) := by
  exact isClopen_univ

example {α : Type} [TopologicalSpace α] : IsClopen (∅ : Set α) := by
  exact isClopen_empty

lemma clopenness_true {i : ℕ} : IsClopen ({ A | A i = true} : Set (ℕ → Bool)) := by
  rw [← @continuous_boolIndicator_iff_isClopen (ℕ → Bool) _ { A | A i = true}]
  unfold Set.boolIndicator
  simp
  exact continuous_apply i

lemma clopenness_false {i : ℕ} : IsClopen ({ A | A i = false} : Set (ℕ → Bool)) := by
  rw [← @continuous_boolIndicator_iff_isClopen (ℕ → Bool) _ { A | A i = false}]
  unfold Set.boolIndicator
  simp
  refine Continuous.comp' ?hg ?hf
  exact { isOpen_preimage := fun s a ↦ a }
  exact continuous_apply i


lemma clopenness {i : ℕ} {b : Bool} : IsClopen ({ A | A i = b} : Set (ℕ → Bool)) := by
  cases b
  exact clopenness_false
  exact clopenness_true

example {α : Type} [TopologicalSpace α] (A B : Set α) (hA : IsClopen A)
  (hB : IsClopen B) : IsClopen (A ∩ B) := by exact IsClopen.inter hA hB

example : IsClopen ({ A | A 0 = true ∧ A 1 = true} : Set (ℕ → Bool)) := by
  change IsClopen ({A : ℕ → Bool | A 0 = true} ∩ {A | A 1 = true})
  apply IsClopen.inter
  exact clopenness_true
  exact clopenness_true

example {k:ℕ} : IsClopen ({ A | ∀ i : Fin k, A i.1 = true} : Set (ℕ → Bool)) := by
  have h₀: ((⋂ i : Fin k, { A | A i.1 = true}) : Set (ℕ → Bool))
    = ({ A | ∀ i : Fin k, A i.1 = true} : Set (ℕ → Bool)) := by ext;simp
  suffices IsClopen ((⋂ i : Fin k, { A | A i.1 = true}) : Set (ℕ → Bool)) by
    rw [← h₀]
    tauto
  apply isClopen_iInter_of_finite
  intro i
  exact clopenness_true

example {k:ℕ} {σ : Fin k → Bool} : IsClopen ({ A | ∀ i : Fin k, A i.1 = σ i} : Set (ℕ → Bool)) := by
  have h₀: ((⋂ i : Fin k, { A | A i.1 = σ i}) : Set (ℕ → Bool))
    = ({ A | ∀ i : Fin k, A i.1 = σ i} : Set (ℕ → Bool)) := by ext;simp
  suffices IsClopen ((⋂ i : Fin k, { A | A i.1 = σ i}) : Set (ℕ → Bool)) by
    rw [← h₀]
    tauto
  apply isClopen_iInter_of_finite
  intro i
  exact clopenness
