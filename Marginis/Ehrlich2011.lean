import Mathlib.Order.RelIso.Basic

/-!

# Conway names, the simplicity hierarchy and the surreal number tree

[PHILIP EHRLICH](http://logicandanalysis.org/index.php/jla/issue/view/5)

A tree ⟨A,<ₛ⟩ is a partially  ordered  class  such  that  for  each x ∈ A,
the  class {y ∈ A : y <ₛ x} of predecessors of x,  written  ‘pr_A(x)’,
is  a  set  well  ordered  by <ₛ.

We prove that the usual ordering of ℕ is a tree in this sense.
-/


instance : PartialOrder ℕ := LinearOrder.toPartialOrder


notation:10 a " <ₛ " b  => a < b
notation:10 a " ≤ₛ " b  => a ≤ b

def pr (x : ℕ) := { y : ℕ // (y <ₛ x) }

instance (x : ℕ) : IsTrichotomous { y : ℕ // y <ₛ x} (λ u v ↦ (u <ₛ v)) := instIsTrichotomousLt
instance (x : ℕ) : IsTrans { y : ℕ // y <ₛ x} (λ u v ↦ (u <ₛ v)) := instIsTransLt
instance (x : ℕ) : IsWellFounded { y : ℕ // y <ₛ x} (λ u v ↦ (u <ₛ v)) := Subtype.wellFoundedLT (fun y ↦ y < x)
instance ehrlich_tree (x : ℕ) : IsWellOrder { y : ℕ // y <ₛ x} (λ u v ↦ (u <ₛ v)) := {} -- no fields are needed since they are all inferred

 /- A maximal subclass wellordered by <ₛ is called a branch.
 Over ℕ we can only prove that all of ℕ itself is a branch.
 -/

def branch (P : ℕ → Prop) := WellFounded (λ a b : { k : ℕ // P k } ↦ a < b) ∧
  ∀ Q : ℕ → Prop, WellFounded (λ a b : { k : ℕ // Q k } ↦ a < b) →
    (∀ k, P k → Q k) → (∀ k, P k ↔ Q k)

lemma branchℕ : branch (λ _ ↦ True) := by
  unfold branch
  constructor
  exact wellFounded_lt
  intro Q _ hQ₁ k
  simp
  tauto

/- More interesting : prefixes of strings.

A linear order satisfies:
le : α → α → Prop
lt : α → α → Prop
le_refl : ∀ (a : α), a ≤ a
le_trans : ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c
lt_iff_le_not_le : ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬b ≤ a
le_antisymm : ∀ (a b : α), a ≤ b → b ≤ a → a = b
min : α → α → α
max : α → α → α
compare : α → α → Ordering
le_total : ∀ (a b : α), a ≤ b ∨ b ≤ a
 -/

def pr' (x : List ℕ) := { y : List ℕ // y <+: x }

lemma le_refl₀ : ∀ (a : List ℕ), a <+: a := fun a ↦ List.prefix_refl a
lemma le_trans₀ : ∀ (a b c : List ℕ), a <+: b → b <+: c → a <+: c :=
  fun _ _ _ a_1 a_2 ↦ List.IsPrefix.trans a_1 a_2

/- This antisymmetry of the prefix relation does not seem to be in Mathlib yet, so we include
it here as a culmination of this analysis of the tree structure of `<+:`. -/

lemma prefix_antisymm
(a b : List ℕ)
(h : a <+: b)
(h₀ : b <+: a)
: a = b := by
    obtain ⟨c,hc⟩ := h
    obtain ⟨d,hd⟩ := h₀
    rw [← hc,List.append_assoc] at hd
    simp at hd
    rw [hd.1] at hc
    simp at hc
    tauto

lemma lt_iff_le_not_le₀ : ∀ (a b : List ℕ), a <+: b ∧ a ≠ b ↔ a <+: b ∧ ¬b <+: a := by
  intro a b
  simp
  intro h
  constructor
  . intro h₀
    contrapose h₀
    simp at *
    apply prefix_antisymm a b h h₀
  . contrapose
    simp
    intro h₀
    subst h₀
    exact h
