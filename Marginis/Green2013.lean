import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Lattice
/- This illustrates the concept of [A]_P from the footnote on the
first page of
`Embedding an analytic equivalence relation in`
`the transitive closure of a Borel relation`
by EDWARD J GREEN.

Specifically, if P is the partition of ℕ into even and odd numbers and
A is the set of prime numbers, then we show that [A]_P = ℕ.
-/


def f : Nat → Fin 2 := λ n ↦ ⟨n % 2,by
  refine Nat.mod_lt n ?_
  exact Nat.zero_lt_succ 1
⟩

def p : ℕ → ℕ → Prop := λ i j ↦ f i = f j

def P : Set (Set ℕ) := {{a | f a = 0},{a | f a = 1}}

def A : Set ℕ := λ i ↦ i.Prime

lemma primes_odd_even : ∀ i : Fin 2, (∃ n, n.Prime ∧ f n = i) := by
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
  let i := f n
  let Q := primes_odd_even i
  unfold A
  unfold p
  obtain ⟨a,ha⟩ := Q
  exists a
  tauto

lemma π_P (n : ℕ) : ∃ π ∈ P, π ∩ A ≠ ∅ := by
  obtain ⟨a,ha⟩ := A_p n
  unfold P
  simp
  by_cases hf : f a = 0
  . left
    suffices ∃ a, f a = 0 ∧ a ∈ A by
      exact Set.nonempty_iff_ne_empty.mp this
    exists a
    tauto
  . right
    suffices ∃ a, f a = 1 ∧ a ∈ A by
      exact Set.nonempty_iff_ne_empty.mp this
    exists a
    constructor
    refine Fin.fin_two_eq_of_eq_zero_iff ?_
    simp
    tauto
    tauto
