/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Halting
import Mathlib.Computability.Primrec
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Computability.NFA
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Digits

/-!

# Effectivizing Lusin’s Theorem

[RUSSELL MILLER](http://logicandanalysis.org/index.php/jla/article/view/382)

The paper discusses Turing degrees among other things.
Here we formalize Turing reducibility (Degrees of unsolvability).

(Mathlib has a `reduce.lean` file that can be reconciled with this.)

This file introduces many-one reducibility (mapping reducibility) and
proves its basic properties.

We work with a couple of classes of functions:
 - mon (which includes both 𝓓₁ and 𝓓ₘ and any monoid of functions)
 - mon₁ (which fits 𝓓₁ and 𝓓ₘ but not as general as mon₁)
 - monₘ (which includes 𝓓ₘ but not 𝓓₁).

We show over mon₁ that the degrees are not rigid, using complementation.

Over monₘ we show that the degrees form an upper semilattice and has
an automorphism that simply swaps ⊥ := ⟦∅⟧ₘ and ⊤ := ⟦ℕ⟧ₘ.

The halting problem `K` is defined in this context and
its basic degree-theoretic properties established.
-/


/-

## m-reducibility

The basic definitions at the level of sets.

-/

/-- An arbitrary monoid. -/
structure mon where
  /-- The functions under consideration (computable, primitive recursive, hyperarithmetic, etc.) -/
  func : (ℕ → ℕ) → Prop
  id : func id
  comp : ∀ {f g}, func f → func g → func (f ∘ g)

/-- The unit monoid consists of `id` only. The corresponding degree structure
has equality as its equivalence.
 -/
def unitMon : mon := {
  func := fun f => f = id
  id := rfl
  comp := fun hf hg => by simp_all}

/-- Embedding on the left over ℕ. -/
def inlFun : ℕ → ℕ := fun k => 2 * k

/-- Embedding on the right over ℕ. -/
def inrFun : ℕ → ℕ := fun k => 2 * k + 1

/-- A monoid in which we can prove ⊕ is an upper bound, even if not the least one. -/
structure mon₁ extends mon where
  inl : func inlFun
  inr : func inrFun

/-- The injective functions ca be used in defining 1-degrees, 𝓓₁. -/
def injClone : mon₁ := {
  func := Function.Injective
  id := fun ⦃a₁ a₂⦄ a ↦ a
  comp := Function.Injective.comp
  inl := mul_right_injective₀ <| Ne.symm (Nat.zero_ne_add_one 1)
  inr := Function.Injective.comp Nat.succ_injective <|mul_right_injective₀ (by simp)
}


/-- Mapping (many-one) reducibility. -/
def m_reducible {m : mon}  (A B : ℕ → Bool) := ∃ f : ℕ → ℕ, m.func f ∧ ∀ x, A x = B (f x)

instance (u : ℕ → ℕ) (n : ℕ):
  Fintype ((Fin (u n) → Bool)) := Pi.fintype


instance (u : ℕ → ℕ) (n : ℕ):
  Fintype ((Fin (u n) → Bool) → Bool) := Pi.fintype

instance (n : ℕ):
  Primcodable ((Fin n → Bool)) := Primcodable.finArrow

instance (u : ℕ → ℕ) (n : ℕ):
  Primcodable ((Fin (u n) → Bool)) := Primcodable.finArrow

instance (k : ℕ) :
  Primcodable ((Fin k.succ → Bool)) := Primcodable.finArrow


-- instance (n : ℕ):
--   Primcodable ((Fin n → Bool) → Bool) := sorry


-- instance (u : ℕ → ℕ) (n : ℕ):
--   Primcodable ((Fin (u n) → Bool) → Bool) := by sorry

instance (u : ℕ → ℕ) :  Denumerable ((n : ℕ) × (Fin (u n) → Bool)) := by
  exact Denumerable.ofEncodableOfInfinite ((n : ℕ) × (Fin (u n) → Bool))



instance : Primcodable ((Fin 2 → Bool)) := Primcodable.finArrow

-- instance : Encodable (Bool → Bool) := Encodable.fintypeArrowOfEncodable

instance : Encodable (Bool → Bool) := by exact Encodable.fintypeArrowOfEncodable
instance : Encodable (List Bool) := by exact List.encodable

instance : Encodable (List (Fin 2)) := by exact List.encodable

def turing_functional' (f : List Bool × ℕ → Part Bool) : Prop :=
  @Partrec (List Bool × ℕ) Bool _ _ f ∧ ∀ u v, u <+: v →
    (f (v, 0)) ≠ Part.none → f (u, 0) ≠ Part.none

def turing_functional (f : List Bool → ℕ → Part Bool) : Prop := by
  let W := @Partrec₂ (List Bool) ℕ Bool _ _ _ f
  exact W ∧ ∀ n u v, u <+: v →
    (f u n) ≠ Part.none → f v n = f v n

def turing_reducible (A B : ℕ → Bool) : Prop :=
  ∃ φ, turing_functional φ ∧ ∀ n, ∃ k, φ (List.ofFn (fun a : Fin k => B a)) n = A n

def get_part (σ : List Bool) (k : ℕ) : Part Bool := σ.get? k

lemma for_refl : Partrec₂ get_part := by
  apply Computable.ofOption
  apply Computable.list_get?

theorem t_refl : Reflexive turing_reducible := by
  intro A
  use fun σ k => σ.get? k
  constructor
  constructor
  · exact for_refl
  · simp
  · intro n
    use n.succ
    simp
    have : ∀ k, (A 0 :: List.ofFn fun i : Fin k ↦ A (i.1 + 1))
                      = List.ofFn fun i : Fin k.succ ↦ A i := by
      intro k
      ext l
      simp
    simp_rw [this n]
    apply List.getElem_ofFn
open Classical



def getlist' (β : ℕ → Part Bool) (l : ℕ)
  (h : ∀ k : Fin l, β k.1 ≠ Part.none) : List Bool := by
  exact List.ofFn (fun k : Fin l => by
    exact (β k.1).get (by
      have : ∃ q, (β k.1) = Part.some q := by exact Part.ne_none_iff.mp (h k)
      simp_all only [ne_eq, Bool.exists_bool]
      cases this with
      | inl h_1 => simp_all only [Part.some_dom]
      | inr h_2 => simp_all only [Part.some_dom]
    )
  )



open Nat
inductive Partrec_in {A : ℕ →. ℕ} : (ℕ →. ℕ) → Prop
  | self : Partrec_in A
  | zero : Partrec_in (pure 0)
  | succ : Partrec_in succ
  | left : Partrec_in fun n : ℕ => n.unpair.1
  | right : Partrec_in fun n : ℕ => n.unpair.2
  | pair {f g} : Partrec_in f → Partrec_in g → Partrec_in fun n => pair <$> f n <*> g n
  | comp {f g} : Partrec_in f → Partrec_in g → Partrec_in fun n => g n >>= f
  | prec {f g} : Partrec_in f → Partrec_in g → Partrec_in (unpaired fun a n =>
      n.rec (f a) fun y IH => do let i ← IH; g (pair a (pair y i)))
  | rfind {f} : Partrec_in f → Partrec_in fun a => rfind fun n => (fun m => m = 0) <$> f (pair a n)

def Computable_in (f g : ℕ → ℕ) :=
  @Partrec_in (g) f

def T_reducible (A B : ℕ → Bool) :=
  Computable_in (fun k => (A k).toNat) (fun k => (B k).toNat)


infix:50 " ≤ₜ " => (fun A B => @Partrec_in B A)

theorem computable_in_refl : Reflexive Computable_in := by
  intro A
  exact Partrec_in.self

open Partrec_in
-- (h : @Partrec_in A f) not assumed explicitly
inductive use_bound {A : ℕ → ℕ} : (ℕ →. ℕ) → ℕ → ℕ → Prop
 | compu {g k} : Partrec g → use_bound g k 0
 | self {k} : use_bound A k k.succ
 | pair {f:ℕ→.ℕ} {g:ℕ→.ℕ} {k uf ug} :
    use_bound f k uf → use_bound g k ug →
    use_bound (fun n => pair <$> f n <*> g n) k (max uf ug)
 | comp {f:ℕ→.ℕ} {g:ℕ→.ℕ} {k uf ug} :
    (h : g k ≠ Part.none) → use_bound f (g k|>.get <|PartENat.ne_top_iff_dom.mp h) uf →
      use_bound g k ug →
        use_bound (fun n => g n >>= f) k (max uf ug)
-- do this for `prec` and `rfind` and then prove that a use exists whenever f is @Partrec_in A
-- and both are total.

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

-- Now we can define Turing equivalence, deduce that it is an equiv.rel., and form the
-- 𝓓ᵀ.
example : Transitive T_reducible := by intro A B C hAB; exact computable_in_trans hAB

example : Reflexive T_reducible := by intro A; apply computable_in_refl

def T_equivalent (A B : ℕ → Bool) := T_reducible A B ∧ T_reducible B A

instance t_equiv_equiv : Equivalence T_equivalent := {
  refl := fun _ => ⟨self, self⟩
  symm := by intro A B; exact fun h => ⟨h.2, h.1⟩
  trans := by
    intro A B C h₀ h₁
    exact ⟨computable_in_trans h₀.1 h₁.1, computable_in_trans h₁.2 h₀.2⟩
}

instance 𝓓_setoid : Setoid (ℕ → Bool) := {
  r := T_equivalent
  iseqv := t_equiv_equiv
}
def 𝓓ₜ := Quotient 𝓓_setoid

/-- The Turing degree 0 contains all computable sets, but
 by definition it is just the Turing degree of ∅. -/
instance : Zero 𝓓ₜ := {
  zero := ⟦fun _ => false⟧
}


def turing_reducible' (A B : ℕ →. ℕ) := @Partrec_in B A


instance blah : Encodable (Bool → Bool) := {
  encode := by
    intro σ
    cases σ true
    · cases σ false
      · exact 0
      · exact 1
    · cases σ false
      · exact 2
      · exact 3
  decode := by
    intro n
    by_cases n < 4
    · by_cases n < 3
      · by_cases n < 2
        by_cases n < 1
        · exact some fun _ => false -- n=0
        · exact some fun x => !x -- n=1
        · exact some fun x => x -- n=2
      · exact some fun _ => true -- n=3
    · exact none
  encodek := by
    intro σ
    cases Ht : σ true
    · cases Hf : σ false
      · simp;ext x;cases x <;> tauto
      · simp;ext x;cases x <;> tauto
    · cases Hf : σ false
      · simp;ext x;cases x <;> tauto
      · simp;ext x;cases x <;> tauto
}



lemma encode_decode (k : ℕ) :
    Encodable.encode (@Encodable.decode (Bool → Bool) blah k) = ite (k < 4) k.succ 0 := by
  unfold blah
  simp_all
  split -- this is aesop output
  next h =>
    split
    next h_1 =>
      split
      next h_2 =>
        split
        next h_3 =>
          subst h_3
          simp_all only [ofNat_pos, Encodable.encode_some, succ_eq_add_one, zero_add]
        next h_3 =>
          simp_all only [Encodable.encode_some, succ_eq_add_one, add_left_inj]
          suffices k = 1 by
            subst this
            aesop
          omega
      next h_2 =>
        simp_all only [not_lt, Encodable.encode_some, succ_eq_add_one, reduceAdd, reduceEqDiff]
        exact Nat.eq_of_le_of_lt_succ h_2 h_1
    next h_1 =>
      simp_all only [not_lt, Encodable.encode_some, succ_eq_add_one, reduceAdd, reduceEqDiff]
      exact Nat.eq_of_le_of_lt_succ h_1 h
  next h => simp_all only [not_lt, Encodable.encode_none]

instance blah₂: Primcodable (Bool → Bool) := {
  encode := by
    intro σ
    cases σ true
    · cases σ false
      · exact 0
      · exact 1
    · cases σ false
      · exact 2
      · exact 3
  decode := by
    intro n
    by_cases n < 4
    · by_cases n < 3
      · by_cases n < 2
        by_cases n < 1
        · exact some fun _ => false -- n=0
        · exact some fun x => !x -- n=1
        · exact some fun x => x -- n=2
      · exact some fun _ => true -- n=3
    · exact none
  encodek := by
    intro σ
    cases Ht : σ true
    · cases Hf : σ false
      · simp;ext x;cases x <;> tauto
      · simp;ext x;cases x <;> tauto
    · cases Hf : σ false
      · simp;ext x;cases x <;> tauto
      · simp;ext x;cases x <;> tauto
  prim := by
    apply Nat.Primrec.of_eq
    · show Nat.Primrec (fun k => ite (k < 4) k.succ 0)
      exact Primrec.nat_iff.mp <|Primrec.ite
        (PrimrecRel.comp Primrec.nat_lt Primrec.id <|Primrec.const 4) Primrec.succ <|Primrec.const 0
    · intro k
      have W := encode_decode k
      symm
      rw [W]
}

example : Primrec (fun (σ : Bool → Bool) => σ true) := by
  apply Primrec.dom_fintype

example {n : ℕ} : Primrec (fun (σ : Fin n.succ → Bool) => σ 0) := by
  apply Primrec.dom_fintype




/-- A ≡ₘ B ↔ A ≤ₘ B and B ≤ₘ A. -/
def m_equivalent {m : mon} (A B : ℕ → Bool) := @m_reducible m A B ∧ @m_reducible m B A


/-- A ≤ₘ B iff A is many-one reducible to B. -/
infix:50 " ≤ₘ " => m_reducible

/-- A ≡ₘ B iff A is many-one equivalent to B. -/
infix:50 " ≡ₘ " => m_equivalent


/-

## Basic properties of ≤ₘ

-/

/-- m-reducibility is reflexive. -/
lemma m_refl {m : mon} : Reflexive (@m_reducible m ):=
  fun _ => ⟨ id, ⟨m.id, fun _ => rfl⟩⟩

/-- m-reducibility is transitive. -/
lemma m_trans {m : mon} : Transitive (@m_reducible m) := by
  intro _ _ _ ⟨g₁,hg₁⟩ ⟨g₂,hg₂⟩
  use g₂ ∘ g₁
  constructor
  exact m.comp hg₂.1 hg₁.1
  intro x
  rw [hg₁.2 x, hg₂.2 (g₁ x)];rfl

/-- To do calc proofs with m-reducibility we create a Trans instance. -/
instance {m : mon} : Trans (@m_reducible m) (@m_reducible m) (@m_reducible m) := {
  trans := @m_trans m
}


/-

## Basic properties of ≡ₘ

-/

/-- Many-one equivalence is reflexive. -/
lemma m_equiv_refl {m : mon} : Reflexive (@m_equivalent m) := fun _ => ⟨m_refl _, m_refl _⟩

/-- Many-one equivalence is transitive. -/
lemma m_equiv_trans {m : mon} : Transitive (@m_equivalent m) := by
  intro _ _ _ h₁ h₂
  unfold m_equivalent at *
  constructor
  exact m_trans h₁.1 h₂.1
  exact m_trans h₂.2 h₁.2

/-- Many-one equivalence is symmetric. -/
lemma m_equiv_symm {m : mon} : Symmetric (@m_equivalent m) := by
  intro A B h
  unfold m_equivalent at *
  constructor
  tauto;tauto

/-- Many-one equivalence. -/
lemma m_equiv_equiv {m : mon} : Equivalence (@m_equivalent m) :=
{
  refl := m_equiv_refl,
  symm := by have := @m_equiv_symm m; exact this,
  trans := by have := @m_equiv_trans m; exact this
}


/--

## The degree structure 𝓓ₘ, using quotients

`Quot` is like `Quotient` when the relation is not necessarily an equivalence.
We could do: def 𝓓ₘ' := Quot m_equivalent
-/
abbrev 𝓓setoid {m : mon}: Setoid (ℕ → Bool) := {
  r := @m_equivalent m
  iseqv := m_equiv_equiv
}

/-- The many-one degrees. -/
abbrev 𝓓 {m : mon} := @Quotient (ℕ → Bool) <|@𝓓setoid m

/-- Equivalent reals have equal upper cones. -/
lemma upper_cones_eq {m : mon} (A B : ℕ → Bool) (h : @m_equivalent m A B) :
    @m_reducible m A = @m_reducible m B :=
  Set.ext <| fun _ => Iff.intro (m_trans h.2) (m_trans h.1)

/-- Equivalent reals have equal degrees. -/
lemma degrees_eq {m : mon} (A B : ℕ → Bool) (h : @m_equivalent m A B) :
    @m_equivalent m A = @m_equivalent m B :=
  Set.ext <| fun _ => Iff.intro (m_equiv_trans (m_equiv_symm h)) (m_equiv_trans h)

/-- As an auxiliary notion, we define [A]ₘ ≤ b to mean
that the degree of A is below the degree b. -/
def le_m' {m : mon} (A : ℕ → Bool) (b : @𝓓 m) : Prop := by
  apply Quot.lift
  · intro C D
    intro (hCD : m_equivalent C D)
    show @m_reducible m A C = @m_reducible m A D
    exact eq_iff_iff.mpr <| Iff.intro (fun h => m_trans h hCD.1) fun h => m_trans h hCD.2
  · exact b

/-- The ordering of the m-degrees. -/
def le_m {m : mon} (a b : @𝓓 m) : Prop := by
  apply Quot.lift
  · intro C D
    intro (hCD : C ≡ₘ D)
    show le_m' C b = le_m' D b
    simp only [eq_iff_iff]
    unfold le_m'
    apply Eq.to_iff
    congr
    exact Set.ext fun A => ⟨m_trans hCD.2, m_trans hCD.1⟩
  · exact a

/-

## Basic properties of the m-degrees

-/

/-- The ordering of m-degrees is reflexive. -/
lemma le_m_refl {m : mon} : Reflexive <|@le_m m :=
  Quot.ind <| fun _ => m_refl _

/-- The ordering of m-degrees is transitive. -/
lemma le_m_trans {m : mon} : Transitive <|@le_m m :=
  Quot.ind fun _ => Quot.ind fun _ => Quot.ind fun _ h => m_trans h

/-- m-reducibility is a preorder. -/
def m_degrees_preorder {m : mon} : Preorder (ℕ → Bool) :=
  @Preorder.mk (ℕ → Bool) {le := @m_reducible m}
  {lt := fun A B => m_reducible A B ∧ ¬ m_reducible B A}
    m_refl m_trans (by
      simp only;
      exact fun u v => by unfold m_reducible; trivial
    )

/-- For example 𝓓₁ is a partial order (if not a semilattice). -/
instance {m : mon}: PartialOrder <|@𝓓 m := {
  le := le_m
  le_refl := le_m_refl
  le_trans := le_m_trans
  le_antisymm := Quotient.ind <| fun A => Quotient.ind <| fun B h₁ h₂ => Quotient.sound ⟨h₁,h₂⟩
}

/-- The nontrivial computable sets form the m-degree `0`. -/
instance {m : mon} : Zero (@𝓓 m) := {
  zero := ⟦ (fun k => ite (k=0) true false) ⟧
}

/-- The degree ⟦∅⟧ₘ = ⊤. -/
instance {m : mon} : Bot (@𝓓 m) := {
  bot := ⟦ (fun _ => false) ⟧
}

/-- The degree ⟦ℕ⟧ₘ = ⊤. -/
instance {m : mon} : Top (@𝓓 m) := {
  top := ⟦ (fun _ => true) ⟧
}

/--

  ## The recursive join A ⊕ B.

(However, the symbol ⊕ has a different meaning in Lean.)
It is really a shuffle or ♯ (backslash sha).
-/
def join (A B : ℕ → Bool) := fun k => ite (Even k) (A (k/2)) <| B (k/2)

/-- Make sure ♯ binds stronger than ≤ₘ. -/
infix:70 " ⊕ " => join


/-- Join works as desired on the left. -/
lemma join_inl (A B : ℕ → Bool) (k : ℕ): (join A B) (inlFun k) = A k := by
  unfold join inlFun
  simp

/-- Join works as desired on the right. -/
lemma join_inr (A B : ℕ → Bool) (k : ℕ): (join A B) (inrFun k) = B k := by
  unfold join inrFun
  simp only [Nat.not_even_bit1, ↓reduceIte]
  congr
  omega


/-- A ≤ₘ A ⊕ B. -/
lemma join_left {m : mon₁}  (A B : ℕ → Bool) : @m_reducible m.tomon A (A ⊕ B) :=
  ⟨fun k => 2 * k, m.inl, fun k => .symm <| join_inl A B k⟩

/-- B ≤ₘ A ⊕ B. -/
lemma join_right {m : mon₁} (A B : ℕ → Bool) : @m_reducible m.tomon B (A ⊕ B) :=
  ⟨fun k => 2 * k + 1, m.inr, fun k => .symm <|join_inr A B k⟩




open Classical

/-- A map on 𝓓ₘ that swaps ∅ and ℕ. -/
noncomputable def botSwap {m : mon} : @𝓓 m → @𝓓 m := fun a =>
  ite (a = ⊥) ⊤ (ite (a = ⊤) ⊥ a)


/-- Swapping ∅ and ℕ is injective on 𝓓ₘ. -/
theorem botSwap_inj {m : mon} : Function.Injective <| @botSwap m := by
  intro a b h
  unfold botSwap at h
  split_ifs at h with g₀ g₁ g₂ g₃ g₄ g₅
  · exact Eq.trans g₀ g₁.symm
  · exact False.elim <|(g₂ ▸ g₁) h
  · exact False.elim <| g₂ h.symm
  · exfalso;apply g₃ ▸ h ▸ g₀;rfl
  · exact g₃ ▸ g₅.symm
  · exact False.elim <| g₄ h.symm
  · exact False.elim <| g₃ h
  · exact False.elim <| g₀ h
  · exact h

/-- Swapping ∅ and ℕ is surjective on 𝓓ₘ. -/
theorem botSwap_surj {m : mon} : Function.Surjective <| @botSwap m := by
  · unfold botSwap
    intro b
    by_cases H : b = ⊥
    · subst H
      use ⊤
      simp
    · by_cases H : b = ⊤ <;> aesop

/-- In 𝓓ₘ, ⊥ is not below ⊤. -/
lemma emp_not_below {m : mon} : ¬ (⊥ : @𝓓 m) ≤ ⊤ := fun ⟨f,hf⟩ => by simp at hf

/-- In 𝓓ₘ, ⊤ is not below ⊥. -/
lemma univ_not_below {m : mon} : ¬ (⊤ : @𝓓 m) ≤ ⊥ := fun ⟨f,hf⟩ => by simp at hf

/-- In 𝓓ₘ, ⊥ is a minimal element. -/
theorem emp_min {m : mon} : ∀ (a : @𝓓 m), (h : a ≤ ⊥) →  a = ⊥ := by
  apply Quotient.ind
  intro A ⟨f,hf⟩

  unfold 𝓓 𝓓setoid m_equivalent m_reducible at *
  simp_all only [Quotient.eq]
  apply Quot.sound
  have : A = fun _ => false := by ext x; exact hf.2 x
  constructor
  use f
  use f
  simp_all

/-- In 𝓓ₘ, ⊤ is a minimal element. -/
theorem univ_min {m : mon} : ∀ (a : @𝓓 m), (h : a ≤ ⊤) →  a = ⊤ := by
  apply Quotient.ind
  intro A ⟨f,hf⟩
  unfold 𝓓 𝓓setoid m_equivalent m_reducible at *
  simp_all only [Quotient.eq]
  apply Quot.sound
  constructor
  use f
  use f
  simp_all

/-- An automorphism of a partial order is a bijection that preserves and reflects
the order. -/
def automorphism {α : Type} [PartialOrder α] (π : α → α): Prop :=
  Function.Bijective π ∧ ∀ a b, a ≤ b ↔ π a ≤ π b

/-- The complement map on `ℕ → Bool`. -/
def cpl : (ℕ → Bool) → (ℕ → Bool) := fun A => (fun k => ! (A k))

/-- The complement map on 𝓓ₘ. -/
def complementMap {m : mon} : @𝓓 m → @𝓓 m := by
  apply Quotient.lift
  intro A B ⟨⟨f₁,hf₁⟩,⟨f₂,hf₂⟩⟩
  show ⟦cpl A⟧ = ⟦cpl B⟧
  exact Quotient.sound <| ⟨⟨f₁,hf₁.1, fun x => by unfold cpl; congr; exact hf₁.2 x⟩,
                           ⟨f₂,hf₂.1, fun x => by unfold cpl; congr; exact hf₂.2 x⟩⟩

/-- In 𝓓ₘ, ⊥ ≠ ⊤. -/
lemma emp_univ_m_degree {m : mon} : (⊥ : @𝓓 m) ≠ ⊤ := by
  intro hc
  have : 𝓓setoid.r (fun _ => false) (fun _ => true) := Quotient.eq''.mp hc
  unfold 𝓓setoid m_equivalent at this
  simp only at this
  obtain ⟨f,hf⟩ := this.1
  simp at hf

/-- The (⊥,⊤) swap map is not the identity. -/
theorem botSwapNontrivial {m : mon} : @botSwap m ≠ id := by
  intro hc
  have : ∀ a, @botSwap m a = id a := by exact fun a ↦ congrFun hc a
  specialize this ⊥

  unfold botSwap at this
  simp_all only [ite_true, id_eq]
  apply emp_univ_m_degree.symm
  exact this

/-- A partial order is rigid if there are no nontrivial automorphisms. -/
def rigid (α : Type) [PartialOrder α] : Prop :=
  ∀ π, @automorphism α _ π → π  = id

/-

## Computability results needed for monₘ
-/

/-- Dividing-by-two is primitive recursive. -/
lemma half_primrec : Primrec (fun k => k/2) :=
  Primrec.of_graph
    ⟨id, ⟨Primrec.id, by
      intro x
      simp only [Encodable.encode_nat, id_eq]
      omega
    ⟩⟩
    (PrimrecRel.comp₂
      Primrec.eq
      (Primrec₂.comp₂ Primrec.nat_div Primrec₂.left <| Primrec₂.const 2)
      Primrec₂.right)

/-- An arithmetical characterization of "Even" is primitive recursive. -/
lemma primrec_even_equiv : PrimrecPred fun k ↦ k / 2 * 2 = k := by
    apply PrimrecRel.comp
    exact Primrec.eq
    apply Primrec.of_graph
    use id
    simp only [Encodable.encode_nat, id_eq]
    exact ⟨Primrec.id, fun x => by omega⟩
    · exact (PrimrecRel.comp₂ Primrec.eq
      (Primrec₂.comp₂ Primrec.nat_mul
        (Primrec₂.comp₂ Primrec.nat_div Primrec₂.left <| Primrec₂.const 2) <| Primrec₂.const 2)
        Primrec₂.right)
    · exact Primrec.id

/-- Characterizing "Even" arithmetically. -/
lemma even_div_two (a : ℕ) : a / 2 * 2 = a ↔ Even a :=
  Iff.intro (fun h => ⟨a / 2, Eq.trans h.symm (mul_two (a/2))⟩) <| Nat.div_two_mul_two_of_even

/-- "Even" is a primitive recursive predicate. -/
lemma even_primrec : @PrimrecPred ℕ _ Even _ :=
  PrimrecPred.of_eq primrec_even_equiv even_div_two


/-- The usual join of functions on ℕ is primitive recursive. -/
theorem primrec_join {f₁ f₂ : ℕ → ℕ} (hf₁ : Primrec f₁) (hf₂ : Primrec f₂) :
    Primrec fun k ↦ if Even k then f₁ (k / 2) else f₂ (k / 2) :=
  Primrec.of_eq
    (Primrec.cond (even_primrec)
      (Primrec.comp hf₁ <|half_primrec)
      (Primrec.comp hf₂ <|half_primrec))
    (by intro n; simp)


/-- The usual join of functions on ℕ is computable. -/
theorem computable_join {f₁ f₂ : ℕ → ℕ} (hf₁ : Computable f₁) (hf₂ : Computable f₂) :
    Computable fun k ↦ if Even k then f₁ (k / 2) else f₂ (k / 2) :=
  Computable.of_eq
    (Computable.cond (Primrec.to_comp even_primrec)
      (Computable.comp hf₁ <|Primrec.to_comp half_primrec)
      (Computable.comp hf₂ <|Primrec.to_comp half_primrec))
    (by intro n; simp)

/-- An auxiliary lemma for proving that the join A₀ ⊕ A₁ is monotone in A₀ within the context
 of the monoid class `mon₁`.-/
lemma getHasIte {m : mon₁} (hasIte₂ : ∀ {f₁ f₂}, m.func f₁ → m.func f₂ → m.func
    fun k ↦ if Even k then f₁ (k / 2) else f₂ (k / 2)) :
    ∀ f, m.func f → m.func (fun k : ℕ => if Even k then f (k / 2) * 2 else k) := by
  intro f hf
  have : (fun k ↦ if Even k then ((fun a => a * 2) ∘ f) (k / 2) else
          (fun a => 2 * a + 1)  (k / 2))
        = fun k ↦ if Even k then f (k / 2) * 2 else k := by
    ext k
    split_ifs with g₀
    · rfl
    · show 2 * (k/2) + 1 = k
      have ⟨a,ha⟩ := odd_iff_exists_bit1.mp <| Nat.not_even_iff_odd.mp g₀
      subst ha
      omega
  rw [← this]
  exact @hasIte₂ ((fun a => a * 2) ∘ f) (fun a => 2 * a + 1)
    (m.comp (by simp_rw [mul_comm _ 2]; exact m.inl) hf) m.inr

/-

## monₘ : a monoid that is a "clone" and closer to closure under primitive recursion.

-/

/-- Coding two functions into one. -/
def joinFun (f₁ f₂ : ℕ → ℕ) := fun k ↦ if Even k then f₁ (k / 2) else f₂ (k / 2)

/-- Requirement for a semilattice like 𝓓ₘ. -/
structure monₘ extends mon₁ where
  join : ∀ {f₁ f₂}, func f₁ → func f₂ → func (joinFun f₁ f₂)
  const : ∀ c, func (fun _ => c)

structure monₜₜ extends monₘ where
  ttrefl : func fun n ↦
    Encodable.encode
      ((Denumerable.ofNat ((k : ℕ) × (Fin k.succ → Bool)) n).snd
        ↑(Denumerable.ofNat ((k : ℕ) × (Fin k.succ → Bool)) n).fst)

def tt_reducible (A B : ℕ → Bool) := ∃ u : ℕ → ℕ, (Computable u ∧ Monotone u) ∧
  ∃ Φ : (n : ℕ) → (Fin (u n) → Bool) → Bool,
  Computable (fun pair : (n : ℕ) × (Fin (u n) → Bool) => Φ pair.1 pair.2) ∧
    ∀ x, A x = Φ x (fun i => B i)

-- def tt_reducible_mon {m : monₜₜ} (A B : ℕ → Bool) := ∃ u : ℕ → ℕ, (Computable u ∧ Monotone u) ∧
--   ∃ Φ : (n : ℕ) → (Fin (u n) → Bool) → Bool,
--   Computable (fun pair : (n : ℕ) × (Fin (u n) → Bool) => Φ pair.1 pair.2) ∧
--     ∀ x, A x = Φ x (fun i => B i)


example {k : ℕ} : Computable (fun (σ : Fin k.succ → Bool) => σ 0) := by
  refine Primrec.to_comp ?hf
  apply Primrec.dom_fintype



/-- The computable functions satisfy the requirement for a semilattice like 𝓓ₘ. -/
def comput : monₘ := {
  func  := Computable
  id    := Computable.id
  comp  := Computable.comp
  inl   := Primrec.to_comp Primrec.nat_double
  inr   := Primrec.to_comp <| Primrec.nat_double_succ
  join  := computable_join
  const := Computable.const
}

/-- The primitive recursive functions satisfy the requirement for a semilattice like 𝓓ₘ. -/
def primrec : monₘ := {
  func := Primrec, id := Primrec.id, comp := Primrec.comp, inl := Primrec.nat_double,
  inr := Primrec.nat_double_succ, join := primrec_join, const := Primrec.const
}

/-- The all-monoid, which will give us only three degrees, ⊥, ⊤ and 0. -/
def allMon : monₘ := {
  func := fun _ => True, id := trivial, comp := fun _ _ => trivial,
  inl := trivial, inr := trivial, join := fun _ _ => trivial, const := fun _ => trivial
}

/-- The join A₀ ⊕ A₁ is monotone in A₀. -/
theorem join_le_join {m : monₘ} {A₀ A₁ : ℕ → Bool} (h : @m_reducible m.tomon A₀ A₁) (B : ℕ → Bool) :
    @m_reducible m.tomon (A₀ ⊕ B) (A₁ ⊕ B) := by
  obtain ⟨f,hf⟩ := h
  use fun k => ite (Even k) (f (k/2) * 2) k
  constructor
  · exact getHasIte m.join _ hf.1
  · intro k
    unfold join
    split_ifs with g₀ g₁
    · rw [Nat.mul_div_left (f (k / 2)) Nat.zero_lt_two]
      exact hf.2 _
    · exact False.elim <| g₁ <| Nat.even_mul.mpr <| .inr <| Nat.even_iff.mpr rfl
    · rfl

/-- The join is bounded by each upper bound. -/
lemma join_le {m : monₘ} {A B C : ℕ → Bool} (h₁ : @m_reducible m.tomon A C)
    (h₂ : @m_reducible m.tomon B C) : @m_reducible m.tomon (join A B) C := by
  obtain ⟨f₁,hf₁⟩ := h₁
  obtain ⟨f₂,hf₂⟩ := h₂
  use fun k => ite (Even k) (f₁ (k/2)) (f₂ (k/2))
  constructor
  · exact m.join hf₁.1 hf₂.1
  · intro k
    unfold join
    split_ifs with h
    exact hf₁.2 (k/2)
    exact hf₂.2 (k/2)


/-- The m-degree `[A]ₘ ⊔ b`. -/
def join' {m : monₘ} (A : ℕ → Bool) (b : Quot <|@m_equivalent m.tomon) :
    Quot <|@m_equivalent m.tomon := by
  apply Quot.lift
  show ∀ B C, @m_equivalent m.tomon B C →
    Quot.mk m_equivalent (join A B) = Quot.mk m_equivalent (join A C)
  intro B C h;
  apply Quot.sound
  unfold m_equivalent at *
  constructor
  · apply join_le
    apply join_left
    calc
      B ≤ₘ C := h.1
      _ ≤ₘ _ := @join_right m.tomon₁ _ _
  · apply join_le
    apply join_left
    calc
      C ≤ₘ B := h.2
      _ ≤ₘ _ := @join_right m.tomon₁ _ _
  exact b



/-- 𝓓ₘ is a join-semilattice. -/
instance {m : monₘ}: SemilatticeSup <|@𝓓 m.tomon := {
  le := le_m
  le_refl := le_m_refl
  le_trans := le_m_trans
  le_antisymm := Quotient.ind <| fun A => Quotient.ind <| fun B h₁ h₂ => Quotient.sound ⟨h₁,h₂⟩

  le_sup_left  := Quotient.ind fun A => Quotient.ind fun B => by apply join_right
  le_sup_right := Quotient.ind fun A => Quotient.ind fun B => by apply join_left
  sup_le := Quotient.ind fun A => Quotient.ind fun B => Quotient.ind fun C h₁ h₂ => by
    exact join_le h₂ h₁
  sup := fun a => by
    apply Quotient.lift
    intro A B h
    show join' A a = join' B a
    unfold join'
    congr
    exact funext <| fun C => Quot.sound ⟨join_le_join h.1 C, join_le_join h.2 C⟩
}



/-- This is false for 1-degrees.
However, the complementing automorphism works there.
-/
theorem emp_univ {m : monₘ} (B : ℕ → Bool) (h_2 : ¬(⟦B⟧ : @𝓓 m.tomon) = ⟦ (fun _ => false) ⟧ ) :
    (⟦ (fun _ => true) ⟧ : @𝓓 m.tomon) ≤ ⟦B⟧ := by
  unfold 𝓓setoid m_equivalent m_reducible at *
  by_cases H : B = (fun _ => false)
  · subst H
    exfalso
    apply h_2
    rfl
  · have ⟨k,hk⟩ : ∃ k, B k ≠ false := by
      contrapose H
      simp_all only [ne_eq, Bool.not_eq_false, not_exists, Bool.not_eq_true, Decidable.not_not]
      ext x;tauto
    use fun _ => k
    simp_all only [ne_eq, Bool.not_eq_false, implies_true, and_true]
    exact m.const k

/-- In the m-degrees, if ⟦B⟧ ≠ ⊤ then ⊥ ≤ ⟦B⟧. -/
theorem univ_emp {m : monₘ} (B : ℕ → Bool) (h_2 : ⟦B⟧ ≠ (⊤ : @𝓓 m.tomon) ) :
    (⊥ : @𝓓 m.tomon) ≤ ⟦B⟧ := by
  unfold 𝓓 𝓓setoid m_equivalent m_reducible at *
  by_cases H : B = (fun _ => true)
  subst H
  exfalso
  apply h_2
  rfl
  have ⟨k,hk⟩ : ∃ k, B k ≠ true := by
    contrapose H
    simp_all only [ne_eq, Bool.not_eq_true, not_exists, Bool.not_eq_false, Decidable.not_not]
    ext x;tauto
  use fun _ => k
  simp_all only [ne_eq, Bool.not_eq_true, implies_true, and_true]
  exact m.const k

/-- The complement map is not the identity map of 𝓓ₘ. -/
theorem complementMapIsNontrivial {m : mon} : @complementMap m ≠ id := by
  intro hc
  have : @complementMap m ⟦fun _ => false⟧ = ⟦fun _ => false⟧ := by rw [hc]; simp
  unfold complementMap cpl at this
  simp only [Quotient.lift_mk, Bool.not_false, Quotient.eq] at this
  obtain ⟨f,hf⟩ := this.1
  simp at hf

/-- The complement map is a surjective map of 𝓓ₘ. -/
theorem complementMap_surjective {m : mon} : Function.Surjective <|@complementMap m := by
  unfold complementMap
  apply Quotient.ind
  intro A
  use ⟦ cpl A ⟧
  simp only [Quotient.lift_mk, Quotient.eq]
  unfold cpl
  simp only [Bool.not_not]
  exact ⟨⟨id, m.id, by tauto⟩, ⟨id, m.id, by tauto⟩⟩

/-- The complement map is an injective map of 𝓓ₘ. -/
theorem complementMap_injective {m : mon} : Function.Injective <|@complementMap m :=
  Quotient.ind fun A => Quotient.ind fun B h => Quotient.sound <| by
  unfold complementMap cpl at h
  simp only [Quotient.lift_mk, Quotient.eq] at h
  obtain ⟨⟨f₁,hf₁⟩, ⟨f₂,hf₂⟩⟩ := h
  simp only at hf₁ hf₂
  exact ⟨⟨f₁, hf₁.1, fun x => by rw [← Bool.not_not <| A x, ← Bool.not_not <| B <| f₁ x, hf₁.2 x]⟩,
         ⟨f₂, hf₂.1, fun x => by rw [← Bool.not_not <| B x, ← Bool.not_not <| A <| f₂ x, hf₂.2 x]⟩⟩

/-- The complement map is an automorphism of 𝓓ₘ. -/
theorem complementMapIsAuto {m : mon} : (@automorphism (@𝓓 m)) complementMap :=
    ⟨⟨complementMap_injective, complementMap_surjective⟩,
    Quotient.ind fun A => Quotient.ind fun B => by
      constructor
      · intro ⟨f,hf⟩
        use f
        unfold cpl
        tauto
      · exact fun ⟨f,hf⟩ => ⟨f, hf.1, fun x => (Bool.not_not <| B <| f x) ▸
          (Bool.not_not <| A <| x) ▸ congrArg (fun b => !b) (hf.2 x)⟩⟩

/-- 𝓓ₘ is not rigid. -/
theorem notrigid {m : mon} : ¬ rigid (@𝓓 m) := by
  unfold rigid
  push_neg
  exact ⟨complementMap, complementMapIsAuto, complementMapIsNontrivial⟩


/-- Over a rich enough monoid, `botSwap` is an automorphism. -/
theorem botSwapIsAuto {m : monₘ} : (@automorphism (@𝓓 m.tomon)) botSwap :=
  ⟨⟨botSwap_inj, botSwap_surj⟩,
    Quotient.ind fun A => Quotient.ind fun B => by
      unfold botSwap
      split_ifs with g₀ g₁ g₂ g₃ g₄ g₅ g₆ g₇
      · rw [g₀,g₁];simp
      · rw [g₀,g₂]
        exact ⟨fun h => False.elim <| emp_not_below h, fun h => False.elim <| univ_not_below h⟩
      · exact g₀ ▸ ⟨fun _ => emp_univ B g₁, fun _ => univ_emp B g₂⟩
      · rw [g₃,g₄]
        exact ⟨fun h => False.elim <| univ_not_below h, fun h => False.elim <| emp_not_below h⟩
      · simp only [le_refl, iff_true];rw [g₃, g₅];
      · rw [g₃]
        exact ⟨fun _ => univ_emp B g₅, fun _ => emp_univ B g₄⟩
      · rw [g₆]
        exact ⟨fun h => False.elim <|  g₀ <| emp_min ⟦A⟧ h,
              fun h => False.elim <|  g₃ <| univ_min ⟦A⟧ h⟩
      · exact g₇ ▸ ⟨fun h => False.elim <| g₃ <| univ_min ⟦A⟧ h,
                    fun h => False.elim <| g₀ <| emp_min ⟦A⟧ h⟩
      · tauto⟩


/-- In 𝓓ₘ, the degree of ∅ is less than 0. -/
lemma emp_lt_zero {m : monₘ} : ⊥ < (0 : @𝓓 m.tomon) := by
  refine lt_of_le_not_le ?_ ?_
  · use fun _ => 1
    simp only [one_ne_zero, ↓reduceIte, implies_true, and_true]
    exact m.const 1
  · intro ⟨f,hf⟩
    simp at hf

/-- ∅ and ℕ are the minimal elements of 𝓓ₘ. -/
lemma zero_one_m {E : monₘ} {b : Bool} (A : ℕ → Bool) :
    A ≠ (fun _ => b) ↔ @m_reducible E.tomon (fun _ => !b) A := by
  constructor
  · intro hA
    unfold m_reducible
    contrapose hA
    simp_all only [not_exists, not_and, not_forall, Bool.not_not_eq, ne_eq, Decidable.not_not]
    ext n
    have ⟨_,ha⟩ := hA (fun _ ↦ n) (E.const _)
    exact ha.symm
  · intro ⟨g,hg⟩ hc
    subst hc
    simp_all


open Classical

/-- The eth r.e. set -/
noncomputable def φ {e : Nat.Partrec.Code} : ℕ → Bool := fun n => (Nat.Partrec.Code.eval e n).Dom


/-- Defining the halting set K as {e | φₑ(0)↓}.
(There are other possible, essentially equivalent, definitions.) -/
noncomputable def K : ℕ → Bool := fun e =>
  (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) 0).Dom

/-- The halting set K is r.e. -/
theorem K_re : RePred fun k ↦ (K k) = true := by
  unfold K
  have Q := ComputablePred.halting_problem_re 0
  simp_all only [decide_eq_true_eq]
  show RePred fun l => (fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom)
    ((fun k ↦ Denumerable.ofNat Nat.Partrec.Code k) l)
  unfold RePred at *
  show Partrec fun l =>
    ( fun a : Nat.Partrec.Code ↦ Part.assert
      ((fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom) a) fun _ ↦ Part.some ())
    ((fun k ↦ Denumerable.ofNat Nat.Partrec.Code k) l)
  let f := ( fun a : Nat.Partrec.Code ↦ Part.assert
      ((fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom) a) fun _ ↦ Part.some ())
  show Partrec fun l =>
    f
    ((fun k ↦ Denumerable.ofNat Nat.Partrec.Code k) l)
  apply Partrec.comp
  exact Q
  exact Computable.ofNat Nat.Partrec.Code

/-- The complement of the halting set K is not r.e. -/
theorem Kbar_not_re : ¬RePred fun k ↦ (!K k) = true := by
  unfold K
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  intro hc
  have h₀ : (fun c : Nat.Partrec.Code ↦ ¬(c.eval 0).Dom)
           = fun c ↦ ¬((Denumerable.ofNat Nat.Partrec.Code (Encodable.encode c)).eval 0).Dom := by
    simp only [Denumerable.ofNat_encode]
  exact ComputablePred.halting_problem_not_re 0 <| h₀ ▸ Partrec.comp hc Computable.encode

/-- The complement of the halting set K is not computable. -/
theorem Kbar_not_computable : ¬ Computable fun k => ! K k := by
  intro hc
  have : ComputablePred fun k ↦ K k = false := by
    refine ComputablePred.computable_iff.mpr ?_
    use fun k => ! K k
    simp only [Bool.not_eq_true', and_true]
    exact hc
  exact Kbar_not_re <| ComputablePred.to_re (by simp_all)

/-- The halting set K is not computable. -/
theorem K_not_computable : ¬ Computable K :=
  fun hc => Kbar_not_computable
    <| Computable.cond hc (Computable.const false) (Computable.const true)

def 𝓓ₘ := @𝓓 comput.tomon

/-- If B is computable and A ≤ₘ B then A is computable. -/
theorem compute_closed_m_downward (A B : ℕ → Bool) (h : Computable B)
    (h₀ : @m_reducible comput.tomon A B) : Computable A := by
  obtain ⟨f,hf⟩ := h₀
  have : A = B ∘ f := by ext k; simp_all
  rw [this]
  apply Computable.comp h
  exact hf.1

/-- If B is r.e. and A ≤ₘ B then A is r.e. -/
theorem re_closed_m_downward {A B : ℕ → Bool} (h : RePred (fun (k : ℕ) => (B k = true)))
    (h₀ : @m_reducible comput.tomon A B) : RePred (fun (k : ℕ) => (A k = true)) := by
  obtain ⟨f,hf⟩ := h₀
  have : A = B ∘ f := by ext k; simp_all
  rw [this]
  unfold RePred at *
  simp_all only [Function.comp_apply, implies_true, and_true]
  exact Partrec.comp h hf

/-- The complement of K is not m-reducible to K. -/
theorem Kbar_not_below_K : ¬ @m_reducible comput.tomon (fun k ↦ (!K k) = true) K := by
  intro hc
  have : RePred (fun (k : ℕ) => (! K k = true)) := re_closed_m_downward K_re (by simp_all)
  have := Kbar_not_re
  simp_all
