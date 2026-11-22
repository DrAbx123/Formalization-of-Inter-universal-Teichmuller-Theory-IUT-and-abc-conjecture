import Mathlib
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S3108RootSqActual

/-- The concrete prime label `l = 5` used by S1280. -/
abbrev fiveLabel : PrimeGeFive := S1280Five

/-- The actual Definition 3.1 field `F` from S1280. -/
abbrev F : Type := (S1280Arithmetic fiveLabel).F

local instance : Field F := (S1280Arithmetic fiveLabel).fieldF

/-- The Gaussian polynomial `X^2 + 1` over the actual field `F`. -/
def p : Polynomial F := Polynomial.X ^ 2 - Polynomial.C (-1)

/-- The actual square root of `-1` in `F[X]/(X^2+1)`. -/
def root : AdjoinRoot p := AdjoinRoot.root p

/-- The actual root squares to `-1`. -/
theorem root_sq : root ^ 2 = -1 := by
  change AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C (-1)) ^ 2 = -1
  have h := AdjoinRoot.eval₂_root p
  simp [p, eval₂_sub, eval₂_pow, eval₂_C, eval₂_X] at h
  exact eq_neg_of_add_eq_zero_left h

#check root_sq
#print axioms root_sq

end LeanFormal.IUT.XiFPaper.S3108RootSqActual
end
