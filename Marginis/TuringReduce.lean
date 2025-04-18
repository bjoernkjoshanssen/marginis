/-
Copyright (c) 2025 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Marginis.manyOne
/-!

# The countability of Aut(𝓓ₜ), the automorphism group of the Turing degrees

This is a famous result within computability theory, due to Slaman and Woodin.
See Corollary 6.3.2 at https://math.berkeley.edu/~slaman/talks/sw.pdf

Here we develop just enough to *state* the result.

-/

open Nat
inductive Partrec_in (A : ℕ →. ℕ) : (ℕ →. ℕ) → Prop
  | self : Partrec_in A A
  | zero : Partrec_in A (pure 0)
  | succ : Partrec_in A succ
  | left : Partrec_in A fun n : ℕ => n.unpair.1
  | right : Partrec_in A fun n : ℕ => n.unpair.2
  | pair {f g} : Partrec_in A f → Partrec_in A g → Partrec_in A fun n => pair <$> f n <*> g n
  | comp {f g} : Partrec_in A f → Partrec_in A g → Partrec_in A fun n => g n >>= f
  | prec {f g} : Partrec_in A f → Partrec_in A g → Partrec_in A (unpaired fun a n =>
      n.rec (f a) fun y IH => do let i ← IH; g (pair a (pair y i)))
  | rfind {f} : Partrec_in A f → Partrec_in A fun a => rfind fun n => (fun m => m = 0) <$> f (pair a n)

def Computable_in (f g : ℕ → ℕ) :=
  Partrec_in g f

def T_reducible (A B : ℕ → Bool) :=
  Computable_in (fun k => (A k).toNat) (fun k => (B k).toNat)

infix:50 " ≤ₜ " => (fun A B => Partrec_in B A)

theorem computable_in_refl : Reflexive Computable_in := by
  intro A
  exact Partrec_in.self

open Partrec_in

/-- ∀ B, B ≤ₜ C → (∀ A, A ≤ₜ B → A ≤ₜ C). -/
theorem computable_in_trans : Transitive Computable_in := fun X Y Z hXY hYZ =>
  @rec _ (fun B _ => ∀ A, A ≤ₜ B → A ≤ₜ Z) (fun _ => id)
  (@rec _ _ zero zero succ left right
    (fun _ _ ↦ pair) (fun _ _ ↦ comp) (fun _ _ ↦ prec) fun _ ↦ rfind)
  (@rec _ _ succ zero succ left right
    (fun _ _ ↦ pair) (fun _ _ ↦ comp) (fun _ _ ↦ prec) fun _ ↦ rfind)
  (@rec _ _ left zero succ left right
    (fun _ _ ↦ pair) (fun _ _ ↦ comp) (fun _ _ ↦ prec) fun _ ↦ rfind)
  (@rec _ _ right zero succ left right
    (fun _ _ ↦ pair) (fun _ _ ↦ comp) (fun _ _ ↦ prec) fun _ ↦ rfind)
  (fun h₀ h₁ _ _ => @rec _ _ (pair h₀ h₁) zero succ left right
    (fun _ _ ↦ pair) (fun _ _ ↦ comp) (fun _ _ ↦ prec) fun _ ↦ rfind)
  (fun h₀ h₁ _ _ => @rec _ _ (comp h₀ h₁) zero succ left right
    (fun _ _ ↦ pair) (fun _ _ ↦ comp) (fun _ _ ↦ prec) fun _ ↦ rfind)
  (fun h₀ h₁ _ _ => @rec _ _ (prec h₀ h₁) zero succ left right
    (fun _ _ ↦ pair) (fun _ _ ↦ comp) (fun _ _ ↦ prec) fun _ ↦ rfind)
  (fun h _ => @rec _ _ (rfind h) zero succ left right
    (fun _ _ ↦ pair) (fun _ _ ↦ comp) (fun _ _ ↦ prec) fun _ ↦ rfind) Y hYZ X hXY

/-- Turing equivalence.-/
def T_equivalent (A B : ℕ → Bool) := T_reducible A B ∧ T_reducible B A

instance T_equiv : Equivalence T_equivalent := {
  refl := fun _ => ⟨self, self⟩
  symm := by intro A B; exact fun h => ⟨h.2, h.1⟩
  trans := by
    intro A B C h₀ h₁
    exact ⟨computable_in_trans h₀.1 h₁.1, computable_in_trans h₁.2 h₀.2⟩
}

instance 𝓓_setoid : Setoid (ℕ → Bool) := {
  r := T_equivalent
  iseqv := T_equiv
}
def 𝓓ₜ := Quotient 𝓓_setoid

/-- The Turing degree 0 contains all computable sets, but
 by definition it is just the Turing degree of ∅. -/
instance : Zero 𝓓ₜ := {
  zero := ⟦fun _ => false⟧
}

lemma T_refl : Reflexive T_reducible := by intro A; apply computable_in_refl

/-- To do calc proofs with m-reducibility we create a Trans instance. -/
instance : Trans (@T_reducible) (@T_reducible) (@T_reducible) := {
  trans := fun h => computable_in_trans h
}

/-- T-reducibility is transitive. -/
lemma T_trans : Transitive (T_reducible) := transitive_of_trans T_reducible

/-- Equivalent reals have equal upper cones. -/
lemma T_upper_cones_eq (A B : ℕ → Bool) (h : T_equivalent A B) :
    T_reducible A = T_reducible B :=
  Set.ext <| fun _ => Iff.intro (T_trans h.2) (T_trans h.1)

/-- Equivalent reals have equal degrees. -/
lemma T_degrees_eq (A B : ℕ → Bool) (h : T_equivalent A B) :
    T_equivalent A = T_equivalent B :=
  Set.ext <| fun _ => Iff.intro (T_equiv.trans h.symm) (T_equiv.trans h)

theorem T_reducible_congr_equiv (A C D : ℕ → Bool) (hCD : T_equivalent C D) :
    (T_reducible A C) = (T_reducible A D) :=
  eq_iff_iff.mpr <| Iff.intro (fun h => T_trans h hCD.1) fun h => T_trans h hCD.2

/-- As an auxiliary notion, we define [A]ₜ ≤ b. -/
def le_T' (A : ℕ → Bool) (b : 𝓓ₜ) : Prop :=
  Quot.lift _ (T_reducible_congr_equiv A) b

theorem T_reducible_congr_equiv' (b : 𝓓ₜ) (C D : ℕ → Bool)
    (hCD : T_equivalent C D) : le_T' C b = le_T' D b := by
  simp only [eq_iff_iff]
  apply Eq.to_iff
  unfold le_T'
  have : T_reducible C = T_reducible D :=
    Set.ext fun _ => ⟨T_trans hCD.2, T_trans hCD.1⟩
  congr

/-- The ordering of the T-degrees. -/
def le_T (a b : 𝓓ₜ) : Prop := Quot.lift _ (T_reducible_congr_equiv' b) a

/-

## Basic properties of the Turing degrees

-/

/-- The ordering of T-degrees is reflexive. -/
lemma le_T_refl : Reflexive le_T :=
  Quot.ind <| fun _ => T_refl _

/-- The ordering of T-degrees is transitive. -/
lemma le_T_trans : Transitive le_T :=
  Quot.ind fun _ => Quot.ind fun _ => Quot.ind fun _ h => T_trans h

/-- T-reducibility is a preorder. -/
def T_degrees_preorder : Preorder (ℕ → Bool) :=
  @Preorder.mk (ℕ → Bool) {le := T_reducible}
  {lt := fun A B => T_reducible A B ∧ ¬ T_reducible B A}
    T_refl T_trans (fun _ _ => by trivial)

/-- 𝓓ₜ is a partial order. -/
instance : PartialOrder 𝓓ₜ := {
  le := le_T
  le_refl := le_T_refl
  le_trans := le_T_trans
  le_antisymm := Quotient.ind fun _ =>
                 Quotient.ind fun _ h₁ h₂ => Quotient.sound ⟨h₁,h₂⟩
}

/-- There is at least one automorphism of 𝓓ₜ, namely the identity.
(In fact it is the only one that is known.) -/
theorem idExists : Nonempty {π : 𝓓ₜ → 𝓓ₜ | automorphism π} :=
  nonempty_subtype.mpr ⟨id, Function.bijective_id, by simp⟩

/-- Slaman and Woodin's Corollary 6.3.2 -/
theorem countableAut : Countable {π : 𝓓ₜ → 𝓓ₜ | automorphism π} := sorry
