import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Bornology


/-
# More reverse mathematics of the Heine-Borel Theorem (2012)
JEFFRY L HIRST & JESSICA MILLER, JLA 2012

On page 2 of the paper,
"X is a subset of [0,1] and for every closed (in the topology on ℝ) subset A ⊆ X, every open cover of A contains a finite sub cover"
Here we prove a modfied version of the Heine-Borel Theorem in the ℝ
-/

open Bornology

-- show that an interval is bounded
lemma bounded_icc {r_c : ℝ} : IsBounded {r | 0 ≤ r ∧ r ≤ r_c} := by
  exact Metric.isBounded_Icc 0 r_c

-- show that [0,1] is bounded
lemma subset_bounded_01 : IsBounded (Set.Icc (0:ℝ) 1) := by
  have := @bounded_icc
  apply this

-- show that X ⊆ [0,1], is bounded
lemma subset_bounded_X  {X : Set ℝ} (hX : X ⊆ (Set.Icc (0:ℝ) 1)): IsBounded X := by
  have := @subset_bounded_01
  exact IsBounded.subset this hX

-- show that A ⊆ X, is bounded
lemma subset_bounded_A {X} {A : Set ℝ} (hX : X ⊆ Set.Icc 0 1) (hA : A ⊆ X) : IsBounded A := by
  have := @subset_bounded_X
  exact subset_bounded_X fun ⦃a⦄ a_1 => hX (hA a_1)

-- show that A is compact for every closed subset of A
theorem compact_A {A X : Set ℝ} (hX : X ⊆ (Set.Icc (0:ℝ) 1)) (hA : A ⊆ X) (hClosed: IsClosed A) : IsCompact A := by
  have hBounded : IsBounded A := by
    have := @subset_bounded_X
    apply this
    have := @subset_bounded_A
    exact fun ⦃a⦄ a_1 => hX (hA a_1)
  have := @Metric.isCompact_of_isClosed_isBounded ℝ _
  exact this hClosed hBounded

-- show that every open cover of A contains a finite subcover
theorem finite_subcover_A {I} {A X : Set ℝ} (hX : X ⊆ (Set.Icc (0:ℝ) 1))
    (hA : A ⊆ X) (hClosed : IsClosed A) (U : I → Set ℝ)
    (hOpen : ∀ i, IsOpen (U i)) (hCover : A ⊆ ⋃ i, U i) :
    ∃ (J : Finset I), A ⊆ ⋃ i ∈ J, U i := by
  have hCompact : IsCompact A := compact_A hX hA hClosed
  exact hCompact.elim_finite_subcover U hOpen hCover


/- show that (X ⊆ [0,1], A ⊆ X) doesn't matter
   Heine Borel theorem: X is closed and bounded ↔ X is compact thus every open cover of X has a finite subcover
-/

-- X is closed and bounded → X is compact and thus every open cover of X has a finite subcover
example {I} {X} (hClosed: IsClosed X) (hBounded : IsBounded X) (U : I → Set ℝ) (hOpen : ∀ i, IsOpen (U i)) (hCover : X ⊆ ⋃ i, U i) :
    ∃ (J : Finset I), X ⊆ ⋃ i ∈ J, U i := by
  have := @Metric.isCompact_of_isClosed_isBounded ℝ _
  exact IsCompact.elim_finite_subcover (this hClosed hBounded) U hOpen hCover

-- X is compact → X is closed ∧ bounded
instance : ProperSpace ℝ := by infer_instance

example {X : Set ℝ} (hCompact : IsCompact X) : IsBounded X ∧ IsClosed X := by
  exact And.symm (Metric.isCompact_iff_isClosed_bounded.mp hCompact)
