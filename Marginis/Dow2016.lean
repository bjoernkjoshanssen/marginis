
import Mathlib.Algebra.BigOperators.Group.Finset

import Mathlib.Data.Fin.Basic
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Algebra.Ring.Regular
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Defs


/-!

# PFA and complemented subspaces of ℓ_∞/c₀

[Alan Dow](http://logicandanalysis.org/index.php/jla/article/view/257)

Section 2 of the paper starts:
`Let A_n, n ∈ ℕ be a partition of ℕ into infinite sets.`
Here we prove formally that there exists a partition of ℕ into infinitely many infinite sets.
The idea is to use the 2-adic valuation.
(We first prove it for just two sets as a warmup.)

We also introduce the ideals A⊥ and I (introduced on page 2 of the paper) and prove A⊥ ⊆ I.
-/
def E : Set Nat := λ k ↦ Even k
def O : Set Nat := λ k ↦ Odd k

lemma infiniteEven : Infinite E := by
  refine Set.infinite_coe_iff.mpr ?_
  refine Set.infinite_of_forall_exists_gt ?h
  intro a
  exists 2*a.succ
  constructor
  . exists a.succ
    linarith
  . linarith

lemma infiniteOdd : Infinite O := by
  refine Set.infinite_coe_iff.mpr ?_
  refine Set.infinite_of_forall_exists_gt ?h
  intro a
  exists (2*a).succ
  constructor
  . exists a
  . linarith

lemma disjointEvenOdd : Disjoint E O := by
  unfold E
  unfold O
  refine Set.disjoint_iff_forall_ne.mpr ?_
  intro a ha b hb
  have : ¬ Odd a := by simp_all;exact ha
  exact Ne.symm (ne_of_mem_of_not_mem hb this)

lemma exhaustiveEvenOdd : E ∪ O = Set.univ := by
  unfold E O
  apply Set.ext
  intro x
  simp
  exact Nat.even_or_odd x

def A_Dow : ℕ → Set ℕ := λ n ↦ λ k ↦ padicValNat 2 k = n

lemma exhaustiveA_Dow : ⋃ n : ℕ, A_Dow n = Set.univ := by
  unfold A_Dow
  apply Set.ext
  intro x
  simp
  exists padicValNat 2 x

lemma disjointA_Dow {m n:ℕ} (h : m ≠ n) : Disjoint (A_Dow m) (A_Dow n) := by
  unfold A_Dow
  refine Set.disjoint_iff_forall_ne.mpr ?_
  intro a ha b hb
  contrapose h
  simp at *
  subst h
  rw [← ha,hb]


lemma infiniteA_Dow {n:ℕ} : Infinite (A_Dow n) := by
  refine Set.infinite_coe_iff.mpr ?_
  refine Set.infinite_of_forall_exists_gt ?h
  intro a
  exists 2^n*(2*a+1)
  constructor
  . unfold A_Dow padicValNat
    have : 0 < 2^n*(2*a+1) := by
      exact Fin.size_pos'
    simp
    refine Set.mem_def.mpr ?h.left.a
    rw [dif_pos this]
    refine (multiplicity.unique' ?h.left.a.hk ?h.left.a.hsucc).symm
    exact Nat.dvd_mul_right (2 ^ n) (2 * a + 1)
    intro hc
    obtain ⟨b,hb⟩ := hc
    revert hb
    suffices ¬2 ^ n * (2 * a + 1) = 2 ^ n  * (2 * b) by
      rw [Nat.pow_succ,Nat.mul_assoc]
      tauto
    simp
    have h₀: Even (2*b) := by exact even_two_mul b
    have h₁: Odd (2*a+1) := by exact odd_two_mul_add_one a
    have h₂ : ¬ Even (2*a+1) := by simp_all
    intro hc
    rw [← hc] at h₀
    tauto
  . show a < 2 ^ n * (2 * a + 1)
    calc
    a < 2*a+1 := by
      cases a with
      |zero => simp
      |succ b => linarith
    _ = 1*(2*a+1) := (Nat.one_mul (2 * a + 1)).symm
    _ ≤ 2^n*(2*a+1) := by
      refine Nat.mul_le_mul ?h₁ ?h₂
      exact Nat.one_le_two_pow
      exact Nat.le_refl (2 * a + 1)

def almost_disjoint (B : Set ℕ) (C : ℕ → Set ℕ) : Set ℕ :=
λ n ↦ Finite (Set.inter (C n) B)

def Abot : Set (Set ℕ) := λ B ↦ almost_disjoint B A_Dow = Set.univ

def I_Dow : Set (Set ℕ) := λ B ↦ ∃ n₀, ∀ n, n₀ ≤ n → n ∈ almost_disjoint B A_Dow

lemma AbotI_Dow_contained : Abot ⊆ I_Dow := by
  unfold Abot I_Dow
  intro C hC
  exists 0
  intro n _
  unfold almost_disjoint at *
  rw [hC]
  trivial
