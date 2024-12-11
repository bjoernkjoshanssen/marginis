import Mathlib.Data.Vector.Basic

/-!

# Projective sets, intuitionistically
by Veldman

Definition 29 gives two inductive conditions (i),(ii)
for membership in a set CB.
Condition (iii) states that all members of CB are
given by (i) and (ii).
Here we prove that an analogue of (iii) holds in Lean's
inductive type theory, using the `cases` tactic.

-/

inductive veldman
| i : veldman → veldman
| ii : veldman → veldman
open veldman

lemma iii (x : veldman) : ∃ y, x = i y ∨ x = ii y := by
  cases x with
  | i y => tauto
  | ii y => use y;tauto

inductive veldman₀ (α β: Type)
| i : α → veldman₀ α β
| ii : β → veldman₀ α β

open veldman₀

lemma iii₀ {α β : Type} (x : veldman₀ α β) :
  (∃ y, x = veldman₀.i y) ∨ ∃ y, x = veldman₀.ii y := by
  cases x with
  | i y => tauto
  | ii y => right;use y

lemma intcases (x : ℤ) : x ≤ 0 ∨ 1 ≤ x := by
  cases x with
  |ofNat a =>
    cases a with
    |zero => left;simp
    |succ b =>
      right
      simp
      refine Int.le_add_of_nonneg_left ?ofNat.succ.h.h
      exact Int.ofNat_zero_le b
  |negSucc a => left;exact Int.toNat_eq_zero.mp rfl


inductive my_type
| bob : my_type
| alice : my_type
| charlie : my_type
open my_type

theorem cases3 (dave : my_type) :
  dave = bob ∨ dave = alice ∨ dave = charlie := by
    cases dave
    . tauto
    . tauto
    . tauto


example : bob ≠ alice := noConfusion

structure royale_high :=
  bobby : my_type

example (hi : royale_high) :
  hi.bobby = bob ∨ hi.bobby = alice ∨ hi.bobby = charlie := by
    apply cases3

inductive bff_high
| foo : bff_high
| bff : bff_high → bff_high

inductive bff_h
| bff : bff_h → bff_h

lemma bff_h_none (x : bff_h) : ∃ y, x = bff_h.bff y := by
  cases x with
  |bff y => tauto

open bff_high

lemma bff_injective (x y : bff_high) (h : bff x = bff y) : x = y := by
  injection h

lemma bff_iii (x : bff_high) : x = foo ∨ ∃ y, x = bff y := by
  cases x with
  |foo => tauto
  |bff x => tauto
