import Mathlib.Topology.MetricSpace.PiNat

/-
The paper

Unique paths as formal points
Thierry Coquand, Peter Schuster

mentions Weak König's Lemma.

We (define and) prove:

 - `WKL (Fin 0)` (this is vacuous for any set, not just trees).
 - `WKL (Fin 1)`. This is computable and uses a nice exercise in list induction, `zerolist`.
 - An equivalent, using `Classical.choice`, of `WKL (Fin 2)` at https://github.com/bjoernkjoshanssen/jla/blob/main/2012-dorais-hirst-shafer.lean
 - `¬ WKL ℕ`.

For `Fin 1` the path is indeed (obviously) unique.

-/

def tree {α : Type} (T : Set (List α)) : Prop :=
  ∀ σ ∈ T, ∀ τ, τ <+: σ → τ ∈ T

def has_a_path {α : Type} (T : Set (List α)) : Prop :=
  ∃ p : ℕ → α, ∀ k, List.ofFn (λ i : Fin k ↦ p i.1) ∈ T

def WKL {α : Type} := ∀ T : Set (List α), tree T → Infinite T → has_a_path T

example : @WKL (Fin 0) := by
  intro T _ hi
  exfalso
  contrapose hi
  refine not_infinite_iff_finite.mpr ?_
  exact Subtype.finite


example : ¬ @WKL ℕ := by
  unfold WKL
  push_neg
  use (λ σ ↦ σ.length ≤ 1)
  constructor
  unfold tree
  intro σ hσ
  intro τ hτ
  obtain ⟨u,hu⟩ := hτ
  aesop
  have : (τ ++ u).length ≤ 1 := hσ
  show τ.length ≤ 1
  calc
    τ.length ≤ (τ ++ u).length := by apply List.IsPrefix.length_le;simp
    _        ≤ _ := by exact hσ

  constructor
  exact @Infinite.of_surjective ({σ : List ℕ // σ.length ≤ 1}) ℕ _
    (λ σ ↦ dite (σ.1.length = 0) (λ _ ↦ 0) (λ h ↦ σ.1.get ⟨0,Nat.zero_lt_of_ne_zero h⟩
    )) (by intro n; use ⟨[n],by simp⟩; simp)
  unfold has_a_path
  push_neg
  intro p
  use 2
  show ¬ [p 0,p 1].length ≤ 1
  simp


theorem zerolist : ∀ (σ : List (Fin 1)), σ = List.replicate σ.length 0
| [] => by simp
| a :: y => by
  rw [zerolist y]
  simp only [List.replicate, List.pure_def, List.bind_eq_bind, List.nil_bind, List.cons_ne_self]
  rw [List.length_replicate]
  simp
  exact Fin.fin_one_eq_zero a

example : @WKL (Fin 1) := by
  intro T hT hi
  use (λ _ ↦ 0)
  intro k
  have W := @not_infinite_iff_finite T
  contrapose hi
  rw [W]
  exact @Finite.Set.subset (List (Fin 1))
    {σ | ∃ i : Fin k, σ = List.ofFn (fun j : Fin i ↦ 0)} T (by
      refine finite_iff_exists_equiv_fin.mpr ?_
      use k
      refine Nonempty.intro ?h.val
      simp
      exact {
        toFun := λ σ ↦ ⟨σ.1.length,by
          let ⟨q,hq⟩ := σ.2
          rw [hq]
          rw [List.length_replicate]
          exact q.2
        ⟩
        invFun := λ i ↦ ⟨List.replicate i 0,by
          use i
        ⟩
        left_inv := by
          intro σ
          simp
          let Q := @zerolist σ.1
          simp_rw [← Q]
        right_inv := by
          intro i
          simp
      }

    ) (by
      intro τ hτ
      simp
      use ⟨τ.length,by
          by_contra hc
          simp at hc
          unfold tree at hT
          contrapose hi
          simp

          have Q := @hT τ hτ (List.replicate k 0) (by
            rw [zerolist τ]
            use (List.replicate (τ.length - k) 0)
            have : τ.length = τ.length - k + k := (Nat.sub_eq_iff_eq_add hc).mp rfl
            nth_rewrite 2 [this]
            rw [← List.replicate_add, add_comm]
          )
          exact Q
      ⟩
      exact zerolist τ
    )
