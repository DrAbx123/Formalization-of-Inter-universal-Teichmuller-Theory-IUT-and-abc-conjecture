import Mathlib
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S3108PMapEqAttempt

/-- The concrete prime label `l = 5` used by S1280. -/
abbrev fiveLabel : PrimeGeFive := S1280Five

/-- The actual Definition 3.1 field `F` from S1280. -/
abbrev F : Type := (S1280Arithmetic fiveLabel).F

local instance : Field F := (S1280Arithmetic fiveLabel).fieldF
local instance : NumberField F := (S1280Arithmetic fiveLabel).numberFieldF

/-- The Gaussian polynomial over `ℚ`. -/
def p : Polynomial ℚ := Polynomial.X ^ 2 - Polynomial.C (-1)

/-- Conditional version: if `root : F` satisfies `root^2 = -1`, then
`p` splits over `F` as `(X - root)(X + root)`. -/
theorem S3108_p_map_eq (root : F) (hroot : root ^ 2 = -1) :
    p.map (algebraMap ℚ F) =
      (Polynomial.X - Polynomial.C root) * (Polynomial.X + Polynomial.C root) := by
  simp only [p, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X]
  have h1 : (algebraMap ℚ F) (-1) = root ^ 2 := by
    rw [hroot]
    simp
  rw [h1, Polynomial.C_pow]
  ring

#check S3108_p_map_eq
#print axioms S3108_p_map_eq

end LeanFormal.IUT.XiFPaper.S3108PMapEqAttempt
end
