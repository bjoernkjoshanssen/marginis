/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Halting
import Mathlib.Computability.Primrec
-- import Mathlib.Computability.TuringDegree
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Nat.PartENat
import Mathlib.Logic.Function.CompTypeclasses
import Marginis.manyOne
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

The Turing degrees `𝓓ₜ` are constructed.
-/



/-- The injective functions can be used in defining 1-degrees, 𝓓₁. -/
def injClone : mon₁ := {
  func := Function.Injective
  id := fun ⦃a₁ a₂⦄ a ↦ a
  comp := Function.Injective.comp
  inl := mul_right_injective₀ <| Ne.symm (Nat.zero_ne_add_one 1)
  inr := Function.Injective.comp Nat.succ_injective <|mul_right_injective₀ (by simp)
}


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

/-- Thanks to ChatGPT. -/
def isprefix (u v : ((k : ℕ) × (Fin k → Bool))) : Prop :=
    ∃ (h : u.1 ≤ v.1),  u.2 = v.2 ∘ Fin.castLE h
-- def isPrefix' {k l : ℕ} (u : Fin k → Bool) (v : Fin l → Bool) : Prop :=
--   k ≤ l ∧ ∀ i : Fin k, u i = v (Fin.castLE ‹k ≤ l› i)

/-- Defining Turing functionals without using `List`. -/
def turingFunctional (f : ((k : ℕ) × (Fin k → Bool)) → ℕ → Part Bool) : Prop :=
  Partrec₂ f ∧ ∀ n u v, isprefix u v → (f u n) ≠ Part.none → f u n = f v n

def turingFunctional' (f : ((k : ℕ) × (Fin k → Bool)) → ℕ → Part Bool) : Prop :=
  Partrec₂ f ∧ ∀ n : ℕ, ∀ l : ℕ, ∀ k : Fin l.succ, ∀ v,
    (f ⟨k,v ∘ Fin.castLE (Fin.is_le k)⟩ n) ≠ Part.none →
     f ⟨k,v ∘ Fin.castLE (Fin.is_le k)⟩ n = f ⟨l,v⟩ n

def turing_functional (f : List Bool → ℕ → Part Bool) : Prop := by
  let W := @Partrec₂ (List Bool) ℕ Bool _ _ _ f
  exact W ∧ ∀ n u v, u <+: v →
    (f u n) ≠ Part.none → f u n = f v n

def turingReducible (A B : ℕ → Bool) : Prop :=
  ∃ φ, turingFunctional φ ∧ ∀ n, ∃ k, φ ⟨k, fun a : Fin k => B a⟩ n = A n

-- theorem tRefl : Reflexive turingReducible := by
--   intro A
--   use (fun p n => dite (n < p.1) (fun h => p.2 ⟨n, h⟩) (fun h => Part.none))
--   constructor
--   · constructor
--     · simp
--       unfold Partrec₂
--       unfold Partrec

--       sorry
--     · sorry
--   · sorry


def turing_reducible (A B : ℕ → Bool) : Prop :=
  ∃ φ, turing_functional φ ∧ ∀ n, ∃ k, φ (List.ofFn (fun a : Fin k => B a)) n = A n

def get_part (σ : List Bool) (k : ℕ) : Part Bool := σ.get? k

def getPart (σ : List Bool) (k : ℕ) : Part Bool := σ[k]?

lemma for_refl : Partrec₂ get_part := by
  apply Computable.ofOption
  apply Computable.list_get?

-- lemma forRefl : Partrec₂ getPart := by
--   apply Computable.ofOption
--   sorry


theorem t_refl : Reflexive turing_reducible := by
  intro A
  use fun σ k => σ.get? k
  constructor
  constructor
  · exact for_refl
  · intro n u v ⟨t,ht⟩
    symm at ht
    subst ht
    intro h
    simp at h
    have := @List.getElem?_append_left Bool u t n (by
        have := @List.getElem?_eq Bool u n
        aesop)
    aesop
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

/-- A relativized version of Nat.Partrec.Code. -/
inductive Nat.Partrec_in.Code : Type
  | self : Code -- (A : ℕ →. ℕ)
  | zero : Code
  | succ : Code
  | left : Code
  | right : Code
  | pair : Code → Code → Code
  | comp : Code → Code → Code
  | prec : Code → Code → Code
  | rfind' : Code → Code

compile_inductive% Nat.Partrec_in.Code

open Encodable Denumerable
open Primrec
namespace Nat.Partrec_in.Code
instance instInhabited : Inhabited (Nat.Partrec_in.Code) :=
  ⟨Nat.Partrec_in.Code.self⟩
/-- Returns a code for the constant function outputting a particular natural. -/
protected def const : ℕ → Code
  | 0 => zero
  | n + 1 => comp succ (Code.const n)

theorem const_inj : ∀ {n₁ n₂}, Nat.Partrec_in.Code.const n₁ = Nat.Partrec_in.Code.const n₂ → n₁ = n₂
  | 0, 0, _ => by simp
  | n₁ + 1, n₂ + 1, h => by
    dsimp [Nat.Partrec_in.Code.const] at h
    injection h with h₁ h₂
    simp only [const_inj h₂]

/-- A code for the identity function. -/
protected def id : Code :=
  pair left right

/-- Given a code `c` taking a pair as input, returns a code using `n` as the first argument to `c`.
-/
def curry (c : Code) (n : ℕ) : Code :=
  comp c (pair (Code.const n) Code.id)

/-- An encoding of a `Nat.Partrec.Code` as a ℕ. -/
def encodeCode : Code → ℕ
  | self => 0
  | zero => 1 -- was 0
  | succ => 2 -- was 1
  | left => 3 -- was 2
  | right => 4 -- was 3
  | pair cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 5
  | comp cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) + 5
  | prec cf cg => (2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 1) + 5
  | rfind' cf => (2 * (2 * encodeCode cf + 1) + 1) + 5 -- was + 4

/--
A decoder for `Nat.Partrec_in.Code.encodeCode`, taking any ℕ to the `Nat.Partrec_in.Code` it represents.
-/
def ofNatCode : ℕ → Code
  | 0 => self
  | 1 => zero
  | 2 => succ
  | 3 => left
  | 4 => right
  | n + 5 =>
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => pair (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | false, true  => comp (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true , false => prec (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true , true  => rfind' (ofNatCode m)

/-- Proof that `Nat.Partrec.Code.ofNatCode` is the inverse of `Nat.Partrec.Code.encodeCode` -/
private theorem encode_ofNatCode : ∀ n, encodeCode (ofNatCode n) = n
  | 0 => by simp [ofNatCode, encodeCode]
  | 1 => by simp [ofNatCode, encodeCode]
  | 2 => by simp [ofNatCode, encodeCode]
  | 3 => by simp [ofNatCode, encodeCode]
  | 4 => by simp [ofNatCode, encodeCode]
  | n + 5 => by
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode_ofNatCode m
    have IH1 := encode_ofNatCode m.unpair.1
    have IH2 := encode_ofNatCode m.unpair.2
    conv_rhs => rw [← Nat.bit_decomp n, ← Nat.bit_decomp n.div2]
    simp only [ofNatCode.eq_6]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [m, encodeCode, ofNatCode, IH, IH1, IH2, Nat.bit_val]

instance instDenumerable : Denumerable Code :=
  mk'
    ⟨encodeCode, ofNatCode, fun c => by
        induction c <;> simp [encodeCode, ofNatCode, Nat.div2_val, *],
      encode_ofNatCode⟩

theorem encodeCode_eq : encode = encodeCode :=
  rfl

theorem ofNatCode_eq : ofNat Code = ofNatCode :=
  rfl

theorem encode_lt_pair (cf cg) :
    encode cf < encode (pair cf cg) ∧ encode cg < encode (pair cf cg) := by
  simp only [encodeCode_eq, encodeCode]
  have := Nat.mul_le_mul_right (Nat.pair cf.encodeCode cg.encodeCode) (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 5))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) this, lt_of_le_of_lt (Nat.right_le_pair _ _) this⟩

theorem encode_lt_comp (cf cg) :
    encode cf < encode (comp cf cg) ∧ encode cg < encode (comp cf cg) := by
  have : encode (pair cf cg) < encode (comp cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

theorem encode_lt_prec (cf cg) :
    encode cf < encode (prec cf cg) ∧ encode cg < encode (prec cf cg) := by
  have : encode (pair cf cg) < encode (prec cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

theorem encode_lt_rfind' (cf) : encode cf < encode (rfind' cf) := by
  simp only [encodeCode_eq, encodeCode]
  omega

theorem primrec₂_pair : Primrec₂ pair :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 5)

theorem primrec₂_comp : Primrec₂ comp :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double_succ.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 5)

theorem primrec₂_prec : Primrec₂ prec :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 5)

theorem primrec_rfind' : Primrec rfind' :=
  ofNat_iff.2 <|
    encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <| nat_double_succ.comp <|
          encode_iff.2 <| Primrec.ofNat Code)
        (const 5)

def eval (A : ℕ →. ℕ) : Code → ℕ →. ℕ
  | self => A
  | zero => pure 0
  | succ => Nat.succ
  | left => ↑fun n : ℕ => n.unpair.1
  | right => ↑fun n : ℕ => n.unpair.2
  | pair cf cg => fun n => Nat.pair <$> eval A cf n <*> eval A cg n
  | comp cf cg => fun n => eval A cg n >>= eval A cf
  | prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (eval A cf a) fun y IH => do
        let i ← IH
        eval A cg (Nat.pair a (Nat.pair y i))
  | rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> eval A cf (Nat.pair a (n + m))).map (· + m)

noncomputable def jump' (A : ℕ →. ℕ) : ℕ → Bool := fun e =>
  (Nat.Partrec_in.Code.eval A (Denumerable.ofNat Nat.Partrec_in.Code e) 0).Dom

noncomputable def jump (A : ℕ → Bool) : ℕ → Bool :=
  fun x => jump' (fun x => Part.some (A x).toNat) x

-- A predicate `p` is r.e. in `A` if the function that is `0` when `p` holds
-- and `Part.none` otherwise, is partial recursive in `A`
def REPred_in (A : ℕ →. ℕ)  (p : ℕ → Prop) :=
  Partrec_in A fun a => Part.assert (p a) fun _ => 0

/- A' is r.e. in A. -/
-- theorem K_re_in (A : ℕ → Bool) :
--   REPred_in (fun x => Part.some (A x).toNat) fun k ↦ (jump A k) = true := by
--   unfold jump
--   have Q := ComputablePred.halting_problem_re 0 -- need to relativize this
--   sorry

end Nat.Partrec_in.Code

def Computable_in (f g : ℕ → ℕ) :=
  Partrec_in g f

def T_reducible (A B : ℕ → Bool) :=
  Computable_in (fun k => (A k).toNat) (fun k => (B k).toNat)


infix:50 " ≤ₜ " => (fun A B => Partrec_in B A)

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
    use_bound (fun n => Nat.pair <$> f n <*> g n) k (max uf ug)
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

## Basic properties of the m-degrees

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

/-- The nontrivial computable sets form the T-degree `0`. -/
instance : Zero 𝓓ₜ := {
  zero := ⟦ fun _ => false ⟧
}

theorem idExists : Nonempty {π : 𝓓ₜ → 𝓓ₜ | automorphism π} :=
  nonempty_subtype.mpr ⟨id, Function.bijective_id, by simp⟩


-- lemma m_implies_T (A B : ℕ → Bool) :
--     @m_reducible comput.tomon A B → T_reducible A B := by
--   intro ⟨f,hf⟩
--   unfold T_reducible Computable_in
--   unfold comput at hf
--   have := @Partrec_in.comp (↑fun k ↦ (B k).toNat) f (fun k => (A k).toNat)
--   -- need comput implies Partrec_in
--   sorry

-- /-- A ≤ₜ A ⊕ B. -/
-- lemma T_join_left (A B : ℕ → Bool) : T_reducible A (A ⊕ B) := by
--   unfold T_reducible
--   unfold join
--   sorry


/-
## A different approach
-/
def turing_reducible' (A B : ℕ →. ℕ) := Partrec_in B A


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



/-- Make sure ♯ binds stronger than ≤ₘ. -/
infix:70 " ⊕ " => join



open Classical



-- instance : PartialOrder 𝓓ₜ := {
--   le := by
--     apply Quot.lift
--     sorry
--     sorry
--   le_refl := sorry
--   le_trans := sorry
--   le_antisymm := sorry
-- }

-- A theorem of Slaman and Woodin: the automorphism group of 𝓓ₜ is countable. -/
-- theorem countableAut : Countable {π : 𝓓ₜ → 𝓓ₜ | automorphism π} := sorry


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


open Classical
