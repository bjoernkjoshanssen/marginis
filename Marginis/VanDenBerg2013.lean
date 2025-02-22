import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Choose.Basic


/-!

# Discretisations of higher order and the theorems of Faa di Bruno and DeMoivre-Laplace

[IMME VAN DEN BERG](http://logicandanalysis.org/index.php/jla/article/view/173)

We formalize Definition 7.3.

-/


def B (ν j : ℕ) : ℚ := ν.choose j * (1/2)^ν

-- For example, 4 choose 2, divided by 16:

#eval B 4 2

-- Note that the assumption j ≤ ν is not needed for Lean to accept the definition, as it will give the value 0 otherwise:

#eval B 2 4

-- Of course, this is sensible since there are no 4-element subsets of a 2-element set.
