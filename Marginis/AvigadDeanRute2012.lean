import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic

/-!

# A metastable dominated convergence theorem

[Jeremy Avigad, Edward T Dean, Jason Rute](http://logicandanalysis.org/index.php/jla/article/view/138)

We prove the equivalence between the two first displayed
equations mentioned on page 2.

-/

section ADR
open Classical
variable (a : ℕ → ℝ)

def P₁ := ∀ ε > 0, ∃ m, ∀ n ≥ m, ∀ n' ≥ m, |a n - a n'| < ε

def P₂ := ∀ ε > 0, ∀ F : ℕ → ℕ, ∃ m,
      ∀ n  ∈ Set.Icc m (F m),
      ∀ n' ∈ Set.Icc m (F m), |a n - a n'| < ε

lemma metastableEquiv₁ : P₁ a → P₂ a := fun h ε hε F => by
  obtain ⟨m,hm⟩ := h ε hε
  use m
  intro n hn n' hn'
  exact hm n hn.1 n' hn'.1


theorem metastableAux {a : ℕ → ℝ} {ε : ℝ} {m : ℕ}  (h : ∃ n ≥ m, ∃ n' ≥ m, ε ≤ |a n - a n'|) :
  ∃ k, ∃ n ∈ Set.Icc m k, ∃ n' ∈ Set.Icc m k, ε ≤ |a n - a n'| := by
    let n := Nat.find h
    let hn := Nat.find_spec h
    let n' := Nat.find hn.2
    have := Nat.find_spec hn.2
    exact ⟨max n n', n, ⟨hn.1, Nat.le_max_left n n'⟩, n', ⟨this.1, Nat.le_max_right n n'⟩, this.2⟩

lemma metastableEquiv₂ : P₂ a → P₁ a := fun h ε hε => by
  specialize h ε hε
  contrapose h
  push_neg at h ⊢
  have Q := fun m => metastableAux <| h m
  exists fun m => Nat.find (Q m)
  exact fun m => Nat.find_spec (Q m)

end ADR
