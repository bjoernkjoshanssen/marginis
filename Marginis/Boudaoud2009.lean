import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.RingTheory.Regular.RegularSequence

/- We define the Lucas sequences from the paper
Decomposition of terms in Lucas sequences
by ABDELMADJID BOUDAOUD
and verify that the Fibonacci sequence appears.
-/

def U (P Q : ℤ) : ℕ → ℤ := λ n ↦ match n with
| 0 => 0
| 1 => 1
| Nat.succ (Nat.succ n) => P * U P Q n.succ - Q * U P Q n

def V (P Q : ℤ) : ℕ → ℤ := λ n ↦ match n with
| 0 => 2
| 1 => P
| Nat.succ (Nat.succ n) => P * V P Q n.succ - Q * V P Q n

-- Fibonacci sequence
#eval λ i : Fin 15 ↦ U 1 (-1) i.1

def D {P Q : ℤ} := P^2 - 4*Q

#eval @D 1 (-1)
