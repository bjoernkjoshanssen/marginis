import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic

/-!

# Decomposition of terms in Lucas sequences

[ABDELMADJID BOUDAOUD](http://logicandanalysis.org/index.php/jla/article/view/18)

We define the Lucas sequences from the paper and verify that the Fibonacci sequence appears.
-/

def U (P Q : ℤ) : ℕ → ℤ := λ n ↦ match n with
| 0 => 0
| 1 => 1
| Nat.succ (Nat.succ n) => P * U P Q n.succ - Q * U P Q n

def V (P Q : ℤ) : ℕ → ℤ := λ n ↦ match n with
| 0 => 2
| 1 => P
| Nat.succ (Nat.succ n) => P * V P Q n.succ - Q * V P Q n

-- #eval λ i : Fin 15 ↦ U 1 (-1) i.1
/-- Fibonacci sequence appearing in Lucas sequence. -/
lemma fibonacciLucas : (λ i : Fin 15 ↦ U 1 (-1) i.1) = ![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377] := by
  decide

def D {P Q : ℤ} := P^2 - 4*Q

#eval @D 1 (-1)
