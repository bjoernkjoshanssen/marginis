import Mathlib.Data.Nat.Prime.Defs

/-!

# Enlargements of schemes

[Lars Brünjes and Christian Serpé](http://logicandanalysis.org/index.php/jla/article/view/160)

-/

/- The equation 2 + 0 = 0 mod p -/
def φ₀ (p:ℕ) := (2 + 0) % p = 0 % p

/- The equation holds mod p for some primes p, but not for all primes p -/
theorem proof_of_concept : ¬ ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → (φ₀ p ↔ φ₀ q) :=
by {
  intro hcontra
  have : φ₀ 2 → φ₀ 3 := (hcontra 2 3 Nat.prime_two Nat.prime_three).mp
  have h3 : φ₀ 3 := this rfl
  have : ¬φ₀ 3 := Nat.ne_of_beq_eq_false rfl
  exfalso
  exact this h3
}


/- Now we consider the existence of a square root of two.
We show it exists for p=2 but not for p=3.
-/
def ψ (p x:ℕ) := (x*x) % p = 2 % p

theorem sqrt_mod2 : ∃ x :ℕ, ψ 2 x  :=
by {
  exists 0
}

theorem sqrt_mod3 : ¬ ∃ x :ℕ, ψ 3 x  :=
by {
  intro hcontra
  rcases hcontra with ⟨x,hx⟩
  have : x % 3 < 3 := Nat.mod_lt x (Nat.succ_pos 2)
  have : x % 3 < 2 ∨ x % 3 = 2 := Nat.lt_succ_iff_lt_or_eq.mp this
  rcases this with hl | he
  have : x % 3 < 1 ∨ x % 3 = 1 := Nat.lt_succ_iff_lt_or_eq.mp hl
  rcases this with Hl | He
  have hz : x % 3 = 0 := Nat.lt_one_iff.mp Hl
  have : (x*x) % 3 = 2 % 3 := hx
  have hzt : 0 = 2 := (calc
  0 = (0 * 0) % 3:= by rfl
  _ = ((x % 3) * (x % 3)) % 3 := by rw [hz.symm]
  _ = (x*x) % 3 := (Nat.mul_mod x x 3).symm
  _ = 2 % 3 := by rw [this])
  have : ¬ 0 = Nat.succ 1 := by exact Nat.ne_of_beq_eq_false rfl
  exact this hzt

  have hzt : 1 = 2 := (calc
  1 = (1 * 1) % 3 := by rfl
  _ = ((x % 3) * (x % 3)) % 3 := by rw [He.symm]
  _ = (x*x) % 3 := (Nat.mul_mod x x 3).symm
  _ = 2 % 3 := hx)
  have : ¬ 1 = Nat.succ 1 := by exact Nat.ne_of_beq_eq_false rfl
  exact this hzt

  have hzt : 1 = 2 := (calc
  1 = (2 * 2) % 3 := by rfl
  _ = ((x % 3) * (x % 3)) % 3 := by rw [he.symm]
  _ = (x*x) % 3 := (Nat.mul_mod x x 3).symm
  _ = 2 % 3 := hx)
  have : ¬ 1 = Nat.succ 1 := by exact Nat.ne_of_beq_eq_false rfl
  exact this hzt

}
