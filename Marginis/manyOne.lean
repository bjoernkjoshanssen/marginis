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
-- import Mathlib.Data.Nat.PartENat
import Mathlib.Logic.Function.CompTypeclasses

/-!
# Many-one reducibility and its automorphisms

Main statements:
* `m_reducible` : m-reducibility
* `
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

/-- Mapping (many-one) reducibility. -/
def m_reducible {m : mon}  (A B : ℕ → Bool) := ∃ f : ℕ → ℕ, m.func f ∧ ∀ x, A x = B (f x)

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


/-- To do calc proofs with m-reducibility we create a Trans instance. -/
instance {m : mon} : Trans (@m_reducible m) (@m_reducible m) (@m_reducible m) := {
  trans := fun ⟨g₁,hg₁⟩ ⟨g₂,hg₂⟩ => by
    use g₂ ∘ g₁
    constructor
    exact m.comp hg₂.1 hg₁.1
    intro x
    rw [hg₁.2 x, hg₂.2 (g₁ x)];rfl
}

/-- m-reducibility is transitive. -/
lemma m_trans {m : mon} : Transitive (@m_reducible m) := transitive_of_trans m_reducible

/--
## The degree structure 𝓓ₘ, using quotients

`Quot` is like `Quotient` when the relation is not necessarily an equivalence.
We could do: def 𝓓ₘ' := Quot m_equivalent
-/
abbrev 𝓓setoid {m : mon} : Setoid (ℕ → Bool) := {
  r := @m_equivalent m
  iseqv := {
    refl := fun _ => ⟨m_refl _, m_refl _⟩
    symm := fun h => ⟨h.2, h.1⟩
    trans := fun h₁ h₂ => ⟨m_trans h₁.1 h₂.1, m_trans h₂.2 h₁.2⟩
}
}

/-- Many-one "equivalence" is indeed an equivalence relation. -/
def m_equiv {m : mon} : Equivalence (@m_equivalent m) := (@𝓓setoid m).iseqv

/-- The many-one degrees. -/
abbrev 𝓓 {m : mon} := Quotient <| @𝓓setoid m

/-- Equivalent reals have equal upper cones. -/
lemma upper_cones_eq {m : mon} (A B : ℕ → Bool) (h : @m_equivalent m A B) :
    @m_reducible m A = @m_reducible m B :=
  Set.ext <| fun _ => Iff.intro (m_trans h.2) (m_trans h.1)

/-- Equivalent reals have equal degrees. -/
lemma degrees_eq {m : mon} (A B : ℕ → Bool) (h : @m_equivalent m A B) :
    @m_equivalent m A = @m_equivalent m B :=
  Set.ext <| fun _ => Iff.intro (m_equiv.trans h.symm) (m_equiv.trans h)

theorem m_reducible_congr_equiv {m : mon} (A C D : ℕ → Bool) (hCD : @m_equivalent m C D) :
    (@m_reducible m A C) = (@m_reducible m A D) :=
  eq_iff_iff.mpr <| Iff.intro (fun h => m_trans h hCD.1) fun h => m_trans h hCD.2


/-- As an auxiliary notion, we define [A]ₘ ≤ b. -/
def le_m' {m : mon} (A : ℕ → Bool) (b : @𝓓 m) : Prop :=
  Quot.lift _ (m_reducible_congr_equiv A) b

theorem m_reducible_congr_equiv' {m : mon} (b : @𝓓 m) (C D : ℕ → Bool)
    (hCD : @m_equivalent m C D) : le_m' C b = le_m' D b := by
  simp only [eq_iff_iff]
  apply Eq.to_iff
  unfold le_m'
  have : @m_reducible m C = @m_reducible m D := Set.ext fun _ => ⟨m_trans hCD.2, m_trans hCD.1⟩
  congr


/-- The ordering of the m-degrees. -/
def le_m {m : mon} (a b : @𝓓 m) : Prop := Quot.lift _ (m_reducible_congr_equiv' b) a


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
@[reducible]
def m_degrees_preorder {m : mon} : Preorder (ℕ → Bool) :=
  @Preorder.mk (ℕ → Bool) {le := @m_reducible m}
  {lt := fun A B => m_reducible A B ∧ ¬ m_reducible B A}
    m_refl m_trans (fun _ _ => by trivial)

/-- For example 𝓓₁ is a partial order (if not a semilattice). -/
instance {m : mon}: PartialOrder <|@𝓓 m := {
  le := le_m
  le_refl := le_m_refl
  le_trans := le_m_trans
  le_antisymm := Quotient.ind fun _ => Quotient.ind fun _ h₁ h₂ => Quotient.sound ⟨h₁,h₂⟩
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

/-- Embedding on the left over ℕ. -/
def inlFun : ℕ → ℕ := fun k => 2 * k

/-- Embedding on the right over ℕ. -/
def inrFun : ℕ → ℕ := fun k => 2 * k + 1


lemma join_inl' (A B : ℕ → Bool) : (A ⊕ B) ∘ inlFun = A := by
  ext
  unfold join inlFun
  simp

/-- Join works as desired on the left. -/
lemma join_inl (A B : ℕ → Bool) (k : ℕ): (A ⊕ B) (inlFun k) = A k := by
  unfold join inlFun
  simp



/-- Join works as desired on the right. -/
lemma join_inr (A B : ℕ → Bool) (k : ℕ): (join A B) (inrFun k) = B k := by
  unfold join inrFun
  simp only [Nat.not_even_bit1, ↓reduceIte]
  congr
  omega

lemma join_inr' (A B : ℕ → Bool) : (A ⊕ B) ∘ inrFun = B := by
  ext k
  exact @join_inr A B k

/-
### MORE POWERFUL MONOIDS

In order to prove all the properties of the join we have to assume `inlFun` and `inrFun`
are in the monoid.
-/

/-- The unit monoid consists of `id` only. The corresponding degree structure
has equality as its equivalence.
 -/
def unitMon : mon := {
  func := fun f => f = id
  id := rfl
  comp := fun hf hg => by simp_all}


/-- A monoid in which we can prove ⊕ is an upper bound, even if not the least one. -/
structure mon₁ extends mon where
  inl : func inlFun
  inr : func inrFun

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
theorem botSwap_inj {m : mon} : Function.Injective <| @botSwap m := fun a b h =>
  by unfold botSwap at h; aesop

/-- Swapping ∅ and ℕ is surjective on 𝓓ₘ. -/
theorem botSwap_surj {m : mon} : Function.Surjective <| @botSwap m := fun b => by
  · unfold botSwap
    by_cases H : b = ⊥
    · use ⊤
      simp_all
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
  simp_all only
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
  simp_all only
  apply Quot.sound
  constructor
  use f
  use f
  simp_all

/-- An automorphism of a partial order is a bijection that preserves and reflects
the order. -/
def automorphism {α : Type} [PartialOrder α] (π : α → α): Prop :=
  Function.Bijective π ∧ ∀ a b, a ≤ b ↔ π a ≤ π b


-- A theorem of Slaman and Woodin: the automorphism group of 𝓓ₜ is countable. -/
-- theorem countableAut : Countable {π : 𝓓ₜ → 𝓓ₜ | automorphism π} := sorry



/-- The complement map on `ℕ → Bool`. -/
def cpl : (ℕ → Bool) → (ℕ → Bool) := fun A k => ! A k

/-- The complement map on `𝓓ₘ`. -/
def complementMap {m : mon} : @𝓓 m → @𝓓 m := by
  apply Quotient.lift
  intro A B ⟨⟨f₁,hf₁⟩,⟨f₂,hf₂⟩⟩
  show ⟦cpl A⟧ = ⟦cpl B⟧
  exact Quotient.sound <| ⟨⟨f₁,hf₁.1, fun x => by unfold cpl; congr; exact hf₁.2 x⟩,
                           ⟨f₂,hf₂.1, fun x => by unfold cpl; congr; exact hf₂.2 x⟩⟩


def induces {m : mon} (f : @𝓓 m → @𝓓 m) (F : (ℕ → Bool) → (ℕ → Bool)) :=
  ∃ hF : (∀ A B : ℕ → Bool, @m_equivalent m A B → @m_equivalent m (F A) (F B)),
    f =  Quotient.lift _ fun A B h => Quotient.sound (hF A B h)

def induced {m : mon} (f : @𝓓 m → @𝓓 m) :=
  ∃ F : (ℕ → Bool) → (ℕ → Bool), induces f F

/-- Induced by a function on ℕ. -/
def induced₀ {m : mon} (π : @𝓓 m → @𝓓 m) := ∃ f : ℕ → ℕ, induces π (fun A => A ∘ f)

/-- The identity automorphism is induced by a function on ℕ. -/
theorem id_induced₀ {m : mon} :
  induced₀ (id : @𝓓 m → 𝓓) := ⟨id, (fun _ _ => id), funext <| Quot.ind <| fun _ => rfl⟩


/-- The complement automorphism is not induced by a function on ℕ. -/
theorem complementMap_is_not_induced₀ {m : mon} :
  ¬ induced₀ (@complementMap m) := by
  intro ⟨f,h₀,h₁⟩
  have ⟨⟨g₀,h₀⟩,_⟩ : @m_equivalent m (cpl (fun _ => false)) ((fun _ => false) ∘ f) :=
    Quotient.eq''.mp <| congrFun h₁ ⊥
  simp [cpl] at h₀

theorem complementMap_is_induced {m : mon} :
  induced (@complementMap m) := by
  use cpl
  use (by
    intro A B ⟨⟨f₁,hf₁⟩,⟨f₂,hf₂⟩⟩
    exact ⟨⟨f₁,hf₁.1, fun x => by unfold cpl; congr; exact hf₁.2 x⟩,
           ⟨f₂,hf₂.1, fun x => by unfold cpl; congr; exact hf₂.2 x⟩⟩)
  rfl



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
  have : @botSwap m ⊥ = id ⊥ := congrFun hc ⊥

  unfold botSwap at this
  simp_all only [ite_true, id_eq]
  apply emp_univ_m_degree.symm
  exact this

/-- A partial order is rigid if there are no nontrivial automorphisms. -/
def rigid (α : Type) [PartialOrder α] : Prop :=
  ∀ π, @automorphism α _ π → π  = id

/-


/-- The injective functions can be used in defining 1-degrees, 𝓓₁. -/
def injClone : mon₁ := {
  func := Function.Injective
  id := fun ⦃_ _⦄ a ↦ a
  comp := Function.Injective.comp
  inl := mul_right_injective₀ (Nat.zero_ne_add_one 1).symm
  inr := Function.Injective.comp Nat.succ_injective <|mul_right_injective₀
    (Nat.zero_ne_add_one 1).symm
}

instance (u : ℕ → ℕ) (n : ℕ) : Fintype ((Fin (u n) → Bool)) := Pi.fintype
instance (u : ℕ → ℕ) (n : ℕ) : Fintype ((Fin (u n) → Bool) → Bool) := Pi.fintype
instance (n : ℕ) : Primcodable ((Fin n → Bool)) := Primcodable.finArrow
instance (u : ℕ → ℕ) (n : ℕ) : Primcodable ((Fin (u n) → Bool)) := Primcodable.finArrow
instance (k : ℕ) : Primcodable ((Fin k.succ → Bool)) := Primcodable.finArrow
instance (u : ℕ → ℕ) :  Denumerable ((n : ℕ) × (Fin (u n) → Bool)) :=
  Denumerable.ofEncodableOfInfinite ((n : ℕ) × (Fin (u n) → Bool))
instance : Primcodable ((Fin 2 → Bool)) := Primcodable.finArrow
-- instance : Encodable (Bool → Bool) := Encodable.fintypeArrowOfEncodable
instance : Encodable (Bool → Bool) := by exact Encodable.fintypeArrowOfEncodable
instance : Encodable (List Bool) := by exact List.encodable
instance : Encodable (List (Fin 2)) := by exact List.encodable

def getlist' (β : ℕ → Part Bool) (l : ℕ)
  (h : ∀ k : Fin l, β k.1 ≠ Part.none) : List Bool :=
    List.ofFn (fun k : Fin l => (β k.1).get (by
      have : ∃ q, (β k.1) = Part.some q := Part.ne_none_iff.mp (h k)
      simp_all only [ne_eq, Bool.exists_bool]
      cases this with
      | inl h_1 => simp_all only [Part.some_dom]
      | inr h_2 => simp_all only [Part.some_dom]))

open Nat

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


instance EBB : Encodable (Bool → Bool) := {
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
    Encodable.encode (@Encodable.decode (Bool → Bool) EBB k) = ite (k < 4) k.succ 0 := by
  unfold EBB
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

instance EBB₂: Primcodable (Bool → Bool) := {
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

example : Primrec (fun (σ : Bool → Bool) => σ true) := Primrec.dom_fintype _
example {n : ℕ} : Primrec (fun (σ : Fin n.succ → Bool) => σ 0) := Primrec.dom_fintype _


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
lemma even_primrec : @PrimrecPred ℕ _ Even  :=
  PrimrecPred.of_eq primrec_even_equiv even_div_two


/-- The usual join of functions on ℕ is primitive recursive. -/
theorem primrec_join {f₁ f₂ : ℕ → ℕ} (hf₁ : Primrec f₁) (hf₂ : Primrec f₂) :
    Primrec fun k ↦ if Even k then f₁ (k / 2) else f₂ (k / 2) :=
  sorry
  -- Primrec.of_eq
  --   (Primrec.cond (even_primrec)
  --     (Primrec.comp hf₁ <|half_primrec)
  --     (Primrec.comp hf₂ <|half_primrec))
  --   (by intro n; simp)


/-- The usual join of functions on ℕ is computable. -/
theorem computable_join {f₁ f₂ : ℕ → ℕ} (hf₁ : Computable f₁) (hf₂ : Computable f₂) :
    Computable fun k ↦ if Even k then f₁ (k / 2) else f₂ (k / 2) :=
  sorry
  -- Computable.of_eq
  --   (Computable.cond (Primrec.to_comp even_primrec)
  --     (Computable.comp hf₁ <|Primrec.to_comp half_primrec)
  --     (Computable.comp hf₂ <|Primrec.to_comp half_primrec))
  --   (by intro n; simp)

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


lemma botSwap_is_induced_helper
  {m : monₘ}
  {A B : ℕ → Bool}
  (hAB : @m_equivalent m.tomon₁.tomon A B) :
  @m_reducible m.tomon₁.tomon
  (if A = fun _ ↦ false then fun _ ↦ true else if A = fun _ ↦ true then fun _ ↦ false else A)
  (if B = fun _ ↦ false then fun _ ↦ true else if B = fun _ ↦ true then fun _ ↦ false else B)
  := by
      by_cases h₀ : A = fun _ => false
      · subst h₀
        by_cases h₁ : B = fun _ => false
        · subst h₁
          simp
          use id
          simp
          exact m.id
        · rw [if_neg h₁]
          simp
          by_cases h₂ : B = fun _ => true
          · subst h₂
            simp
            exact hAB.2 -- faster than exfalso
          · rw [if_neg h₂]
            have ⟨k,hk⟩ : ∃ k, B k = true := by
              by_contra hc
              push Not at hc
              apply h₁
              simp at hc
              exact (Set.eqOn_univ B fun _ ↦ false).mp fun ⦃x⦄ _ ↦ hc x
            use fun _ => k
            simp
            constructor
            · exact m.const k
            · exact hk
      · rw [if_neg h₀]
        by_cases h₁ : A = fun _ => true
        · subst h₁
          simp
          clear h₀
          by_cases h₂ : B = fun _ => false
          · subst h₂
            simp
            exact hAB.2
          · rw [if_neg h₂]
            have : B = fun _ => true := by
              ext k
              obtain ⟨f,hf⟩ := hAB.2
              have := hf.2 k
              simp at this
              exact this
            subst this
            simp
            apply m_refl
        · rw [if_neg h₁]
          by_cases h₂ : B = fun _ => false
          · subst h₂
            exfalso
            apply h₀
            ext k
            obtain ⟨f,hf⟩ := hAB.1
            have := hf.2 k
            simp at this
            exact this
          · rw [if_neg h₂]
            by_cases h₃ : B = fun _ => true
            · subst h₃
              have : A = fun _ => true := by
                ext k
                obtain ⟨f,hf⟩ := hAB.1
                have := hf.2 k
                simp at this
                exact this
              subst this
              exfalso
              apply h₁
              simp
            · rw [if_neg h₃]
              exact hAB.1

/-- The `botSwap` automorphism is induced by a function on reals. -/
theorem botSwap_is_induced {m : monₘ} : induced (@botSwap m.tomon₁.tomon) := by
  let f := fun _ : ℕ => false
  let t := fun _ : ℕ => true
  let m' := m.tomon₁.tomon
  let s : (ℕ → Bool) → (ℕ → Bool) := fun A => if A = f then t else if A = t then f else A
  have h : ∀ (A B : ℕ → Bool), @m_equivalent m' A  B →
    @m_equivalent m' (s A) (s B) := by
    intro A B hAB
    constructor
    · apply botSwap_is_induced_helper hAB
    · apply botSwap_is_induced_helper hAB.symm
  have h' : ∀ (A B : ℕ → Bool), (@𝓓setoid m').r A B →
    (⟦s A⟧ : @𝓓 m') = (⟦s B⟧ : @𝓓 m') := by
    intro A B hAB
    specialize h A B hAB
    simp_all only [Quotient.eq]
    exact h
  use fun A => ite (A = f) t <| ite (A = t) f A, h
  apply funext
  intro a
  symm
  unfold botSwap
  split_ifs with g₀ g₁
  · subst g₀
    show Quotient.lift (fun a ↦ ⟦if a = f then t else if a = t then f else a⟧) h' ⟦f⟧ = ⟦t⟧
    simp
  · subst g₁
    show Quotient.lift (fun a ↦ ⟦if a = f then t else if a = t then f else a⟧) h' ⟦t⟧ = ⟦f⟧
    simp_all only [Quotient.lift_mk, ↓reduceIte, ite_self, m', s, f, t]
  · suffices ∀ a, ¬a = ⊤ →  ¬a = ⊥ → Quotient.lift
      (fun a ↦ ⟦if a = f then t else if a = t then f else a⟧) h' a = a by exact this a g₁ g₀
    apply Quot.ind
    intro A h₀ h₁
    rw [show (⊤ : @𝓓 m') = Quot.mk 𝓓setoid.r t by rfl] at h₀
    rw [show (⊥ : @𝓓 m') = Quot.mk 𝓓setoid.r f by rfl] at h₁
    apply Quot.sound
    have h₀ := @Quot.lift_mk (ℕ → Bool) (Quotient 𝓓setoid) (@m_equivalent m')
      (fun A => (⟦s A⟧ : @𝓓 m')) h' f
    have g₂ : A ≠ t := by
      contrapose! g₀
      simp_all only
    have g₃ : A ≠ f := by
      contrapose! g₀
      simp_all only
    simp_all only [↓reduceIte, ne_eq]
    exact Quotient.eq''.mp rfl



-- def tt_reducible_mon {m : monₜₜ} (A B : ℕ → Bool) := ∃ u : ℕ → ℕ, (Computable u ∧ Monotone u) ∧
--   ∃ Φ : (n : ℕ) → (Fin (u n) → Bool) → Bool,
--   Computable (fun pair : (n : ℕ) × (Fin (u n) → Bool) => Φ pair.1 pair.2) ∧
--     ∀ x, A x = Φ x (fun i => B i)


example {k : ℕ} : Computable (fun (σ : Fin k.succ → Bool) => σ 0) := by
  refine Primrec.to_comp ?hf
  sorry
  -- apply Primrec.dom_fintype



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
    by_cases h : Even k
    · exact if_pos h ▸ if_pos h ▸ hf₁.2 (k/2)
    · exact if_neg h ▸ if_neg h ▸ hf₂.2 (k/2)


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
  le_antisymm  := Quotient.ind fun A => Quotient.ind fun B h₁ h₂ => Quotient.sound ⟨h₁,h₂⟩
  le_sup_left  := Quotient.ind fun A => Quotient.ind fun B => by apply join_right
  le_sup_right := Quotient.ind fun A => Quotient.ind fun B => by apply join_left
  sup_le :=       Quotient.ind fun A => Quotient.ind fun B => Quotient.ind fun C h₁ h₂ => by
    exact join_le h₂ h₁
  sup := fun a => by
    apply Quotient.lift
    intro A B h
    show join' A a = join' B a
    unfold join'
    congr
    exact funext <| fun C => Quot.sound ⟨join_le_join h.1 C, join_le_join h.2 C⟩
}



/-- If b ≠ ⊥ then ⊤ ≤ b. This is false for 1-degrees.
However, the complementing automorphism works there.
-/
theorem emp_univ {m : monₘ} (B : ℕ → Bool) (h_2 : ¬(⟦B⟧ : @𝓓 m.tomon) = ⊥ ) :
    ⊤ ≤ (⟦B⟧ : @𝓓 m.tomon) := by
  unfold 𝓓setoid m_equivalent m_reducible at *
  by_cases H : B = (fun _ => false)
  · subst H
    exfalso
    apply h_2
    rfl
  · have ⟨k,hk⟩ : ∃ k, B k ≠ false := by
      contrapose H
      simp_all only [ne_eq, Bool.not_eq_false, not_exists, Bool.not_eq_true]
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
    simp_all only [ne_eq, Bool.not_eq_true, not_exists, Bool.not_eq_false]
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

/-- Complementation is an automorphism not only of the partial order 𝓓ₘ,
but of the preorder `m_reducible`! (That is true for Turing degrees too.
To rule out that there is an automorphism of the preorder
for Turing degrees that maps something to an element of a different Turing degree
we would have to rule out e.g. a homeomorphism inducing an automorphism.
)
-/
theorem cplAuto {m : mon} (A B : ℕ → Bool) :
  @m_reducible m A B ↔ @m_reducible m (cpl A) (cpl B) := by
      constructor
      · intro ⟨f,hf⟩
        use f
        unfold cpl
        tauto
      · exact fun ⟨f,hf⟩ => ⟨f, hf.1, fun x => (Bool.not_not <| B <| f x) ▸
          (Bool.not_not <| A <| x) ▸ congrArg (fun b => !b) (hf.2 x)⟩

/-- The complement map is an automorphism of 𝓓ₘ. -/
theorem complementMapIsAuto {m : mon} : (@automorphism (@𝓓 m)) complementMap :=
    ⟨⟨complementMap_injective, complementMap_surjective⟩,
    Quotient.ind fun A => Quotient.ind (cplAuto A)⟩

/-- 𝓓ₘ is not rigid. -/
theorem notrigid {m : mon} : ¬ rigid (@𝓓 m) := by
  unfold rigid
  push Not
  exact ⟨complementMap, complementMapIsAuto, complementMapIsNontrivial⟩

-- theorem benchmark

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
  sorry
  -- refine lt_of_le_not_le ?_ ?_
  -- · use fun _ => 1
  --   simp only [one_ne_zero, ↓reduceIte, implies_true, and_true]
  --   exact m.const 1
  -- · intro ⟨f,hf⟩
  --   simp at hf

/-- ∅ and ℕ are the minimal elements of 𝓓ₘ,
since A ≠ ⊥ ↔ ⊤ ≤ A and
A ≠ ⊤ ↔ ⊥ ≤ A.
 -/
lemma zero_one_m {E : monₘ} {b : Bool} (A : ℕ → Bool) :
    A ≠ (fun _ => b) ↔ @m_reducible E.tomon (fun _ => !b) A := by
  constructor
  · intro hA
    unfold m_reducible
    contrapose hA
    simp_all only [not_exists, not_and, not_forall, Bool.not_not_eq]
    ext n
    have ⟨_,ha⟩ := hA (fun _ ↦ n) (E.const _)
    exact ha.symm
  · intro ⟨g,hg⟩ hc
    subst hc
    simp_all

theorem bot_property  {E : monₘ}: ∀  (a : @𝓓 E.tomon), a ≠ ⊥ ↔ ⊤ ≤ a := by
  apply Quot.ind
  intro A
  have := @zero_one_m E false A
  constructor
  · intro h
    simp at this
    show (fun _ => true) ≤ₘ A
    apply this.mp
    revert h
    contrapose
    intro h
    subst h
    rfl
  · intro h
    simp at this
    intro hc
    rw [hc] at h
    revert h
    simp
    exact univ_not_below

theorem top_property  {E : monₘ}: ∀  (a : @𝓓 E.tomon), a ≠ ⊤ ↔ ⊥ ≤ a := by
  apply Quot.ind
  intro A
  have := @zero_one_m E true A
  constructor
  · intro h
    simp at this
    show (fun _ => false) ≤ₘ A
    apply this.mp
    revert h
    contrapose
    intro h
    subst h
    rfl
  · intro h
    simp at this
    intro hc
    rw [hc] at h
    revert h
    simp
    exact emp_not_below

def is_minimal {α : Type*} [PartialOrder α] (a : α) :=
  ∀ b, b ≤ a → b = a


/-- April 17, 2025 -/
theorem bot_is_minimal {E : monₘ} : is_minimal (⊥ : @𝓓 E.tomon) := by
  intro b hb
  have h₀ := @bot_property E b
  by_contra H
  have : ⊤ ≤ b := by simp_all only [ne_eq, not_false_eq_true, true_iff]
  have := le_trans this hb
  revert this
  simp
  exact univ_not_below
  -- More basic proof:
  -- apply Quot.ind
  -- intro B hB
  -- apply Quot.sound
  -- constructor <;> (obtain ⟨f,hf⟩ := hB; use f;)
  -- simp_all

theorem top_is_minimal {E : monₘ} : is_minimal (⊤ : @𝓓 E.tomon) := by
  apply Quot.ind
  intro B hB
  apply Quot.sound
  constructor <;> (obtain ⟨f,hf⟩ := hB; use f;)
  simp_all

theorem only_two_minimals {E : monₘ} (a : @𝓓 E.tomon) : is_minimal a ↔ a = ⊤ ∨ a = ⊥ := by
  constructor
  · intro h
    have h₀ := @top_property E a
    have h₁ := @bot_property E a
    by_contra H
    push_neg at H
    simp_all
    apply emp_univ_m_degree
    have g₀ := h _ h₁
    have g₁ := h _ h₀
    exact g₁.trans g₀.symm
  · intro h
    cases h with
    | inl h => exact h ▸ top_is_minimal
    | inr h => exact h ▸ bot_is_minimal

def is_least {α : Type*} [PartialOrder α] (a : α) :=
  ∀ b, a ≤ b

theorem no_least_if_two_minimal {α : Type*} [PartialOrder α]
    (u v : α) (huv : u ≠ v) (hu : is_minimal u) (hv : is_minimal v) (a : α) :
    ¬ is_least a := fun ha => huv <| (hu a <|ha u).symm.trans (hv a <|ha v)

theorem no_least_m_degree {E : monₘ} (a : @𝓓 E.tomon) : ¬ is_least a := by
  apply no_least_if_two_minimal _ _ _ bot_is_minimal top_is_minimal _
  exact emp_univ_m_degree




open Classical

/-- The eth r.e. set -/
noncomputable def φ {e : Nat.Partrec.Code} : ℕ → Bool := fun n => (Nat.Partrec.Code.eval e n).Dom


/-- Defining the halting set K as {e | φₑ(0)↓}.
(There are other possible, essentially equivalent, definitions.) -/
noncomputable def K : ℕ → Bool := fun e =>
  (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) 0).Dom

/- The halting set K is r.e. -/
-- theorem K_re : RePred fun k ↦ (K k) = true := by
--   unfold K
--   have Q := ComputablePred.halting_problem_re 0
--   simp_all only [decide_eq_true_eq]
--   show RePred fun l => (fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom)
--     ((fun k ↦ Denumerable.ofNat Nat.Partrec.Code k) l)
--   unfold RePred at *
--   show Partrec fun l =>
--     ( fun a : Nat.Partrec.Code ↦ Part.assert
--       ((fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom) a) fun _ ↦ Part.some ())
--     ((fun k ↦ Denumerable.ofNat Nat.Partrec.Code k) l)
--   let f := ( fun a : Nat.Partrec.Code ↦ Part.assert
--       ((fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom) a) fun _ ↦ Part.some ())
--   show Partrec fun l =>
--     f
--     ((fun k ↦ Denumerable.ofNat Nat.Partrec.Code k) l)
--   apply Partrec.comp
--   exact Q
--   exact Computable.ofNat Nat.Partrec.Code

/- The complement of the halting set K is not r.e. -/
-- theorem Kbar_not_re : ¬RePred fun k ↦ (!K k) = true := by
--   unfold K
--   simp only [Bool.not_eq_true', decide_eq_false_iff_not]
--   intro hc
--   have h₀ : (fun c : Nat.Partrec.Code ↦ ¬(c.eval 0).Dom)
--            = fun c ↦ ¬((Denumerable.ofNat Nat.Partrec.Code (Encodable.encode c)).eval 0).Dom := by
--     simp only [Denumerable.ofNat_encode]
--   exact ComputablePred.halting_problem_not_re 0 <| h₀ ▸ Partrec.comp hc Computable.encode

/-- The complement of the halting set K is not computable. -/
theorem Kbar_not_computable : ¬ Computable fun k => ! K k := by
  intro hc
  have : ComputablePred fun k ↦ K k = false := by
    refine ComputablePred.computable_iff.mpr ?_
    use fun k => ! K k
    simp only [Bool.not_eq_true', and_true]
    exact hc
  sorry
  -- exact Kbar_not_re <| ComputablePred.to_re (by simp_all)

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

/- If B is r.e. and A ≤ₘ B then A is r.e. -/
-- theorem re_closed_m_downward {A B : ℕ → Bool} (h : RePred (fun (k : ℕ) => (B k = true)))
--     (h₀ : @m_reducible comput.tomon A B) : RePred (fun (k : ℕ) => (A k = true)) := by
--   obtain ⟨f,hf⟩ := h₀
--   have : A = B ∘ f := by ext k; simp_all
--   rw [this]
--   unfold RePred at *
--   simp_all only [Function.comp_apply, implies_true, and_true]
--   exact Partrec.comp h hf

/-- The complement of K is not m-reducible to K. -/
theorem Kbar_not_below_K : ¬ @m_reducible comput.tomon (fun k ↦ (!K k) = true) K := by
  intro hc
  sorry
  -- have : RePred (fun (k : ℕ) => (! K k = true)) := re_closed_m_downward K_re (by simp_all)
  -- have := Kbar_not_re
  -- simp_all

noncomputable def Km : @𝓓 comput.tomon := ⟦K⟧

noncomputable def Kbarm : @𝓓 comput.tomon := ⟦cpl K⟧

theorem Kbarm_not_below_Km : ¬ Kbarm ≤ Km := by
  unfold Km Kbarm
  have := @Kbar_not_below_K
  simp_all
  exact this

theorem Km_not_below_Kbarm : ¬ Km ≤ Kbarm := by
  intro hc
  have h₀ : @m_reducible comput.tomon K (cpl K) := hc
  have h₁ : @m_reducible comput.tomon (cpl K) (cpl (cpl K)) := by
    have := @complementMapIsAuto comput.tomon
    unfold automorphism at this
    have := @cplAuto comput.tomon K (cpl K)
    tauto
  have h₂ : cpl (cpl K) = K := by unfold cpl;ext;simp
  apply Kbarm_not_below_Km
  rw [h₂] at h₁
  exact h₁

/-- Two m-degrees are automorphic if some automorphism maps one to the other. -/
def automorphic {m : mon} (a b : @𝓓 m) := ∃ π, automorphism π ∧ π a = b

theorem kkbarautomorphic : automorphic Km Kbarm := by
  use complementMap
  constructor
  · exact complementMapIsAuto
  · exact rfl

/-- Surely this should already exist in Mathlib? -/
theorem bijinvfun {α : Type*} [Nonempty α] (f : α → α) (h : Function.Bijective f) :
  Function.Bijective (Function.invFun f) := by
    have h₀ := @Function.invFun_comp α α _ f (Function.Bijective.injective h)
    refine
    (Function.bijective_iff_existsUnique (Function.invFun f)).mpr ?_
    intro b
    use f b
    simp
    constructor
    · show (Function.invFun f ∘ f) b = id b
      rw [h₀]
    · intro y hy
      rw [← hy]
      have : f ∘ (Function.invFun f) = id := by
        apply Function.RightInverse.id
        refine Function.rightInverse_invFun ?h.hf
        exact Function.Bijective.surjective h
      show id y = (f ∘ (Function.invFun f)) y
      rw [this]

theorem automorphism_comp {m : mon} (π : @𝓓 m → 𝓓)
  (hπ : automorphism π) (ρ : 𝓓 → 𝓓)
  (hρ : automorphism ρ) : automorphism (ρ ∘ π) := by
    unfold automorphism at *

    constructor
    · apply Function.Bijective.comp
      tauto
      tauto
    · intro a b
      constructor
      · intro h
        have : π a ≤ π b := (hπ.2 a b).mp h
        have : ρ (π a) ≤ ρ (π b) := (hρ.2 _ _).mp this
        exact this
      · intro h
        have := (hρ.2 (π a) (π b)).mpr h
        exact (hπ.2 _ _).mpr this
def myinst {m : mon} : Equivalence (@automorphic m) := {
  refl := fun x => ⟨id, by
    constructor
    constructor
    · exact Function.bijective_id
    · simp
    simp⟩
  symm := by
    intro x y ⟨π,hπ⟩
    have h₀ := hπ.1.1.1
    have h₁ := hπ.1.1.2
    have H₀ : π ∘ (Function.invFun π) = id := by
      apply Function.RightInverse.id
      exact Function.rightInverse_invFun h₁
    have H₁ (c) : π (Function.invFun π c) = c := by
      show (π ∘ Function.invFun π) c = id c
      rw [H₀]
    use Function.invFun π
    constructor
    · constructor
      · unfold automorphism at hπ
        have := hπ.1.1
        apply bijinvfun _ this
      · intro a b
        have h₂ := hπ.1.2 (Function.invFun π a) (Function.invFun π b)
        constructor
        · intro h
          apply h₂.mpr
          repeat rw [H₁]
          exact h
        · intro h
          repeat rw [H₁] at h₂
          tauto
    · aesop
  trans := by
    intro x y z ⟨π,hπ⟩ ⟨ρ,hρ⟩
    use ρ ∘ π
    constructor
    apply automorphism_comp π hπ.1 ρ hρ.1
    aesop
}

def automorphic_le {m : mon} (a b : @𝓓 m) := ∃ c, a ≤ c ∧ automorphic b c

theorem automorphic_le_refl {m : mon} : Reflexive (@automorphic_le m) := by
  intro a
  use a
  constructor
  exact Preorder.le_refl a
  exact myinst.refl a

theorem automorphic_le_trans {m : mon} : Transitive (@automorphic_le m) := by
  intro a b c ⟨b',hb₁,π,hb₂⟩ ⟨c',hc₁,ρ,hc₂⟩
  unfold automorphic_le
  use π <| ρ c
  constructor
  · apply le_trans hb₁
    rw [← hb₂.2, hc₂.2]
    have := hb₂.1.2 b c'
    tauto
  · use π ∘ ρ
    constructor
    · exact @automorphism_comp m ρ hc₂.1 π hb₂.1
    · simp

instance {m : mon} : Preorder (@𝓓 m) := {
  le :=  @automorphic_le m
  le_refl := automorphic_le_refl
  le_trans := automorphic_le_trans
  lt := fun a b => @automorphic_le m a b ∧ ¬ @automorphic_le m b a
}

/-- is this the same as just automorphic? -/
def automorphic_equiv {m : mon} (a b : @𝓓 m) :=
  @automorphic_le m a b ∧ @automorphic_le m b a
