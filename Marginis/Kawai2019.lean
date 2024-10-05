import Batteries.Data.List.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Measure.Hausdorff

/-

Kawai's 2019 paper "Principles of bar induction and continuity on Baire space"
mentions the Uniform Continuity principle UC that each continuous function

f : (ℕ → Bool) → ℕ

is uniformly continuous.
We prove this. We then prove also that such a function must be bounded.

-/

theorem UC {f : (ℕ → Bool) → ℕ} (hf : Continuous f) : UniformContinuous f :=
  CompactSpace.uniformContinuous_of_continuous hf


lemma getbound {X : Type} [TopologicalSpace X] [CompactSpace X] [Nonempty X] {U : ℕ → Set X}
  (hU : ∀ i, IsOpen (U i)) (h : Set.univ ⊆ ⋃ a : ℕ,     U a) :
                           ∃ k, Set.univ ⊆ ⋃ a : Fin k, U a := by
      obtain ⟨t,ht⟩ := IsCompact.elim_finite_subcover
        CompactSpace.isCompact_univ U hU h
      have hn : t.Nonempty := by
        refine Finset.nonempty_iff_ne_empty.mpr ?_
        intro hc; subst hc; simp at ht
      use (t.max' hn).succ
      intro x hx; let S := ht hx; simp at S; obtain ⟨i, hi⟩ := S; simp;
      use ⟨i, Nat.lt_succ_of_le (Finset.le_max' t i hi.1)⟩; tauto

theorem bounded_of_continuous_compact
   {X : Type} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  (f : X → ℕ) (hf : Continuous f) :
  ∃ a, ∀ A, f A ≤ a := by
  have g₀ (a : ℕ) : IsOpen {A | a > f A} := by
    refine isOpen_lt hf ?hg
    exact continuous_const
  have h₀ : Set.univ ⊆ ⋃ a : ℕ, {A | a > f A} := by
    intro A _; simp; exists (f A).succ; simp
  obtain ⟨k,hk⟩ := getbound g₀ h₀
  simp at hk
  use k
  intro A
  have : A ∈ Set.univ := trivial
  rw [← hk] at this
  simp at this
  obtain ⟨i,hi⟩ := this
  have : i.1 < k := i.2
  linarith

theorem bounded_of_continuous (f : (ℕ → Bool) → ℕ) (hf : Continuous f) :
  ∃ a, ∀ A, f A ≤ a := bounded_of_continuous_compact _ hf
