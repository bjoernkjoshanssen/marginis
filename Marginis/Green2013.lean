import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Lattice
/-!

# Embedding an analytic equivalence relation in the transitive closure of a Borel relation
by EDWARD J GREEN

This illustrates the concept of [A]_P from the footnote on the first page.

Specifically, if P is the partition of ℕ into even and odd numbers and
A is the set of prime numbers, then we show that [A]_P = ℕ.
-/


def f_Green : Nat → Fin 2 := λ n ↦ ⟨n % 2,by
  refine Nat.mod_lt n ?_
  exact Nat.zero_lt_succ 1
⟩

def p : ℕ → ℕ → Prop := λ i j ↦ f_Green i = f_Green j

def P_Green : Set (Set ℕ) := {{a | f_Green a = 0},{a | f_Green a = 1}}

def A : Set ℕ := λ i ↦ i.Prime

lemma primes_odd_even : ∀ i : Fin 2, (∃ n, n.Prime ∧ f_Green n = i) := by
  intro i; by_cases h₀ : i = 0
  . subst h₀; exists 2
  . exists 3
    constructor
    . exact Nat.prime_three
    . symm
      refine Fin.fin_two_eq_of_eq_zero_iff ?_
      tauto

lemma A_p : ∀ n : ℕ, ∃ a ∈ A, p n a := by
  intro n
  let i := f_Green n
  let Q := primes_odd_even i
  unfold A
  unfold p
  obtain ⟨a,ha⟩ := Q
  exists a
  tauto

lemma π_P (n : ℕ) : ∃ π ∈ P_Green, π ∩ A ≠ ∅ := by
  obtain ⟨a,ha⟩ := A_p n
  unfold P_Green
  simp
  by_cases hf : f_Green a = 0
  . left
    suffices ∃ a, f_Green a = 0 ∧ a ∈ A by
      exact Set.nonempty_iff_ne_empty.mp this
    exists a
    tauto
  . right
    suffices ∃ a, f_Green a = 1 ∧ a ∈ A by
      exact Set.nonempty_iff_ne_empty.mp this
    exists a
    constructor
    refine Fin.fin_two_eq_of_eq_zero_iff ?_
    simp
    tauto
    tauto
