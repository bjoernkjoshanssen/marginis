import Mathlib.Topology.Defs.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Homeomorph
/-!

# Preface to the special issue for The Fifth Workshop on Formal Topology
by THIERRY COQUAND
MARIA EMILIA MAIETTI
ERIK PALMGREN

The paper introduces Formal Topology, which is a constructive approach to pointfree topology.
Here we instead look at topologies *with points*, over finite sets and show:
 - there is a unique topology on `Fin 0`;
 - there is a unique topology on `Fin 1`;
 - there exist two distinct topologies on `Fin 2`
 - We also construct the remaining two topologies on `Fin 2` giving a total of 4,
   and show they are homeomorphic.


-/

/-- There is only one topology on `Fin 0`. -/
lemma uniqueTopFin0 ( σ τ : TopologicalSpace (Fin 0)) : σ.IsOpen = τ.IsOpen := by
  apply funext
  intro S
  have : S = ∅ := by
    ext s
    constructor
    . intro
      have Q := s.2
      simp at Q
    . intro h;simp at h
  subst this
  apply propext
  constructor
  . intro; exact @isOpen_empty _ τ
  . intro; exact @isOpen_empty _ σ

/-- There is only one topology on `Fin 0`. -/
lemma uniqueTopFin1 ( σ τ : TopologicalSpace (Fin 1)) : σ.IsOpen = τ.IsOpen := by
  apply funext
  intro S
  by_cases H : S = ∅
  . subst H
    have h₀ := @isOpen_empty _ σ
    have h₁ := @isOpen_empty _ τ
    apply propext
    tauto
  . have : S = Set.univ := by
      ext s
      constructor
      . intro; trivial
      . intro
        have : s = 0 := by exact Fin.fin_one_eq_zero s
        subst this
        have : ∃ a, a ∈ S := by
          refine Set.nonempty_def.mp ?_
          exact Set.nonempty_iff_ne_empty.mpr H
        obtain ⟨a,ha⟩ := this
        have : a = 0 := by exact Fin.fin_one_eq_zero a
        subst this
        tauto
    subst this
    have : σ.IsOpen Set.univ := @TopologicalSpace.isOpen_univ _ σ
    have : τ.IsOpen Set.univ := @TopologicalSpace.isOpen_univ _ τ
    apply propext
    tauto


/-- There are two distinct topologies on `Fin 2`. -/
lemma nonUniqueTopFin2 : ∃ ( σ τ : TopologicalSpace (Fin 2)), σ.IsOpen ≠ τ.IsOpen := by
  use ⊥ -- discrete topology
  use ⊤ -- trivial topology
  intro hc
  have h₀: (⊥ : TopologicalSpace (Fin 2)).IsOpen {0} := trivial

  have : ¬@IsOpen (Fin 2) ⊤ {0} := by
    rw [TopologicalSpace.isOpen_top_iff]
    simp only [Set.singleton_ne_empty, false_or]
    intro h
    cases h.ge (Set.mem_univ 1)

  have h₁: ¬ (⊤ : TopologicalSpace (Fin 2)).IsOpen {0} := by
    change ¬@IsOpen (Fin 2) ⊤ {0} -- thanks to Eric Wieser for this line
    intro hc
    aesop
  aesop

/-- Here are two more topologies on `Fin 2`.
 In fact a topology on `Fin 2` must contain `Set.univ` and `∅`,
 and then there are four possibilities depending on which of `{0}`, `{1}` are included. -/
def mytop (z : Fin 2): TopologicalSpace (Fin 2) :=
{
  IsOpen := λ S ↦ S = ∅ ∨ S = Set.univ ∨ S = {z}
  isOpen_univ := by tauto
  isOpen_inter := by
    intro S T hS hT
    cases hS with
    |inl h => subst h;left;simp
    |inr h =>
      cases h with
      |inl h => subst h; cases hT with
        |inl h => subst h;simp
        |inr h => cases h with
          |inl h => subst h;simp
          |inr h => subst h;simp
      |inr h => subst h;cases hT with
        |inl h => subst h;simp
        |inr h => cases h with
          |inl h => subst h;simp
          |inr h => subst h;simp
  isOpen_sUnion := by
    intro S hS
    simp at hS
    by_cases H₀ : Set.univ ∈ S
    . right;left;refine Set.sUnion_eq_univ_iff.mpr ?_;
      intro a;exists Set.univ
    . by_cases H₁ : {z} ∈ S
      . right;right;ext i;simp;
        constructor
        intro h;
        obtain ⟨t,ht⟩ := h
        let Q := hS t ht.1
        cases Q with
          |inl h => subst h;simp at ht
          |inr h => cases h with
            |inl h => subst h;tauto
            |inr h => subst h;tauto
        intro h
        subst h
        exists {i}
      . left;ext i;simp;intro s hs;
        let Q := hS s hs
        cases Q with
        |inl h => subst h;simp
        |inr h => cases h with
          |inl h => subst h;simp;tauto
          |inr h => subst h;simp;tauto
}

/-- We can show that the latter two topologies are homeomorphic. -/
def myequiv := @Equiv.mk (Fin 2) (Fin 2) (λ x ↦ x + 1) ((λ x ↦ x + 1))
  (by
    refine Function.leftInverse_iff_comp.mpr ?_
    simp only [Fin.isValue, comp_add_right, CharTwo.add_self_eq_zero, add_zero];rfl
  ) (by
    refine Function.rightInverse_iff_comp.mpr ?_
    simp only [Fin.isValue, comp_add_right, CharTwo.add_self_eq_zero, add_zero];rfl
  )

def myhomeo := @Homeomorph.mk (Fin 2) (Fin 2) (mytop 0) (mytop 1) myequiv (by
  refine continuous_def.mpr ?_
  intro S hs
  unfold IsOpen at hs
  have : S = ∅ ∨ S = Set.univ ∨ S = {1} := hs
  show myequiv.toFun ⁻¹' S = ∅ ∨ myequiv.toFun ⁻¹' S = Set.univ ∨ myequiv.toFun ⁻¹' S = {0}
  cases this with
  |inl h => subst h;left;simp
  |inr h => cases h with
    |inl h => subst h;right;left;simp
    |inr h => subst h;right;right;ext x;simp;
              constructor
              . intro h; unfold myequiv at h; simp at h; tauto
              . intro h; subst h;rfl
) (by
  refine continuous_def.mpr ?_
  intro S hs
  unfold IsOpen at hs
  have : S = ∅ ∨ S = Set.univ ∨ S = {0} := hs
  show myequiv.toFun ⁻¹' S = ∅ ∨ myequiv.toFun ⁻¹' S = Set.univ ∨ myequiv.toFun ⁻¹' S = {1}
  cases this with
  |inl h => subst h;left;simp
  |inr h => cases h with
    |inl h => subst h;right;left;simp
    |inr h => subst h;right;right;ext x;simp;
              constructor
              . intro h; unfold myequiv at h; simp at h;
                have : x.1 = 0 ∨ x.1 = 1 := by
                  refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_
                  exact Fin.is_le x
                have : x = 0 ∨ x = 1 := by
                  cases this with
                  | inl h => left;exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h)))
                  | inr h => right;exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h)))
                cases this with
                | inl h₀ => subst h₀;simp at h
                | inr h₀ => subst h₀;rfl
              . intro h; subst h;rfl
)
