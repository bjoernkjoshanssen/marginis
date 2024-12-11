-- import Mathlib.Init.Set
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite

/-!
# An Algebraic Weak Factorisation System on 01-Substitution Sets: A Constructive Proof
by ANDREW SWAN, JLA 2016

On page 2 of the paper,
Perm(𝔸) is the set of all finite permutations of 𝔸, i.e.,
the set of permutations π such that π a = a for all but finitely many a.
We show that Perm(𝔸) is closed under composition and contains the identity.
-/

def moved {A : Type} (f : A → A) : Set A := {a | f a ≠ a}

def perm (A : Type) : Set (A → A) := λ f ↦ Function.Bijective f ∧ Finite (moved f)

theorem perm_comp {A : Type} (f g : perm A) : (f.1 ∘ g.1) ∈ perm A := by
    unfold perm
    constructor
    let hf := f.2.1
    let hg := g.2.1
    exact Function.Bijective.comp hf hg
    let hf := f.2.2
    let hg := g.2.2
    have hf' : Finite ({a | f.1 (g.1 a) ≠ g.1 a}) := by
      unfold moved at *
      let G : {a | f.1 (g.1 a) ≠ g.1 a} → {a | f.1 a ≠ a} := λ a ↦ ⟨g.1 a, a.2⟩
      let Q := Finite.of_injective G
      apply Q
      let R := g.2.1.1
      intro x y h
      have : g.1 x = g.1 y := by
        have h₀: g.1 x = (G x).1 := rfl
        have h₁: g.1 y = (G y).1 := rfl
        rw [h₀,h₁,h]
      let T := R this
      apply SetCoe.ext
      exact T
    unfold moved at *
    have h₀: { a | (f.1 ∘ g.1) a ≠ a} ⊆ {a | g.1 a ≠ a} ∪ {a | f.1 (g.1 a) ≠ g.1 a} := by
      intro a h
      contrapose h
      simp only [ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Function.comp_apply] at *
      rw [h.2]
      tauto
    exact Finite.Set.subset _ h₀

theorem id_perm {A : Type} : id ∈ perm A := by
    unfold perm moved
    constructor
    exact Function.bijective_id
    simp only [id_eq, ne_eq, not_true_eq_false, Set.setOf_false]
    apply Finite.of_fintype
