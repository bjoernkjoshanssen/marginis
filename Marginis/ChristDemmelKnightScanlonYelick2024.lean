import Mathlib.Data.Real.Basic
/-!

# On Multilinear Inequalities of Hölder-Brascamp-Lieb Type for Torsion-Free Discrete Abelian Groups

[MICHAEL CHRIST, JAMES DEMMEL, NICHOLAS KNIGHT, THOMAS SCANLON and KATHERINE YELICK](http://logicandanalysis.org/index.php/jla/article/view/313)

In Section 2.1 it is remarked that
"there is no loss of generality in restricting attention to exponent tuples `s ∈ [0,1]^m`
rather than `s ∈ (0,∞)^m`"
Here we merely establish that this really is a restriction by constructing
an embedding `ι` of the former into the latter.
-/

/-- A finite sequence of numbers in `[0,1]` can be considered to be a finite sequence of numbers
 in `(0,∞)`. -/
def ι {m : ℕ} (s : Fin m → Set.Icc (0:ℝ) 1) : (Fin m → Set.Ici (0:ℝ)) :=
  fun i => ⟨(s i).1, Set.mem_of_mem_inter_left (s i).2⟩
