import Mathlib.Data.Real.Pi.Irrational

/-!

# Models of true arithmetic are integer parts of models of real exponentiation
by MERLIN CARL
LOTHAR SEBASTIAN KRAPP

discusses Schanuel's Conjecture.
Here we would like to consider a simple case of it, such as `e` being transcendental.
For now we simply prove that `q π + r` is irrational for any rational `q ≠ 0` and `r`.

-/

theorem pi_mul_add_rational {q r : ℚ} (h : q ≠ 0) : Irrational (q * Real.pi + r) :=
  fun ⟨p,hp⟩ => irrational_pi ⟨(p - r) / q, by aesop⟩
