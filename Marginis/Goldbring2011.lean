import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int
import Mathlib.Algebra.Group.TypeTags

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.MetricSpace.Basic

import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Quiver.Path
/-

Inspired by the paper

Ends of groups: a nonstandard perspective
Isaac Goldbring

we give a definition of the Cayley graph of a group.
We start from Kyle Miller's Lean 3 code at
https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/graph.2C.20expander.20graph.2C.20cayley.20graph.2C.20.2E.2E.2E.html

After converting that to Lean 4, we construct the Cayley graph of ℤ and give some
computations on it.

We also construct a path in this Cayley graph, using Lean's `Quiver.Path`.

-/


structure digraph (V : Type) (E : Type) :=
(edges : V → V → Set E)

def symmetric_subset (G : Type) [Group G] (S : Set G) : Prop :=
∀ g ∈ S, g⁻¹ ∈ S

def schreier_graph (G : Type) [Group G]
  (S : Set G)
  (X : Type) [MulAction G X] : digraph X G :=
{ edges := λ x y ↦ {g : G | g ∈ S ∧ g • x = y} }

namespace schreier_graph
variable {G : Type} [Group G]
variable {S : Set G}
variable {X : Type} [MulAction G X]

lemma edge_mem (g : G) (x y : X)
  (h : g ∈ (schreier_graph G S X).edges x y) : g ∈ S :=
h.1

lemma edge_gen (g : G) (x y : X)
  (h : g ∈ (schreier_graph G S X).edges x y) : g • x = y :=
h.2

lemma edge_comm_aux {G : Type} [Group G] {S : Set G} {X : Type} [MulAction G X]
{g : G} {x y : X} {sym : symmetric_subset G S} (h : g ∈ (schreier_graph G S X).edges x y)
: g⁻¹ ∈ (schreier_graph G S X).edges y x := by
    constructor
    . exact sym _ (edge_mem g x y h)
    have h₀ : g⁻¹ • (g • x) = g⁻¹ • y := congrArg (HSMul.hSMul g⁻¹) h.2
    have h₁ : g⁻¹ • (g • x) = (g⁻¹ • g) • x := Eq.symm (IsScalarTower.smul_assoc g⁻¹ g x)
    rw [h₁] at h₀; simp at h₀; tauto

lemma edge_comm (g : G) (x y : X) (sym : symmetric_subset G S) :
  g ∈ (schreier_graph G S X).edges x y ↔ g⁻¹ ∈ (schreier_graph G S X).edges y x := by
  constructor
  . intro h; exact @edge_comm_aux G _ S X _ g x y sym h
  . intro h; let Q := @edge_comm_aux G _ S X _ g⁻¹ y x sym h
    simp at Q; tauto

end schreier_graph

def cayley_graph (G : Type) [Group G] (S : Set G) : digraph G G := schreier_graph G S G

namespace cayley_graph
variable {G : Type} [Group G] {S : Set G}

lemma edge_mem (v w g : G)
  (h : g ∈ (cayley_graph G S).edges v w) : g ∈ S :=
h.1

lemma mem_iff (v w g : G) :
  g ∈ (cayley_graph G S).edges v w ↔ g ∈ S ∧ g * v = w := Iff.rfl

lemma apply (v g : G) (h : g ∈ S) : g ∈ (cayley_graph G S).edges v (g * v) := by
  rw [mem_iff]
  simp [h]

end cayley_graph


def IntCayley : digraph ℤ ℤ := @cayley_graph ℤ Multiplicative.group {1,-1}


#check IntCayley.edges 4 5

example : 1 ∈ IntCayley.edges 4 5 := by
  unfold IntCayley cayley_graph schreier_graph
  constructor; tauto; decide

example : 6 ∉ IntCayley.edges 4 5 := by
  unfold IntCayley cayley_graph schreier_graph
  intro hc
  have Q := hc.1
  simp at Q

instance : Quiver ℤ := {
  Hom := λ x y ↦ IntCayley.edges x y
}

def mypath : @Quiver.Path ℤ _ 0 1 := by
  exact @Quiver.Path.cons ℤ _ 0 0 1 (Quiver.Path.nil) (by
    show IntCayley.edges 0 1
    use 1;unfold IntCayley cayley_graph schreier_graph
    simp only;tauto
  )
