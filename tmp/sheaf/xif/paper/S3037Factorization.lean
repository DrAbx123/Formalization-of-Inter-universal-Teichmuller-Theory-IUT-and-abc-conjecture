import tmp.sheaf.xif.paper.S3030AffineOriginClassification
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3037Factorization
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

abbrev R0 : Type := S2801E37CoordinateRing S2844D6F6BaseChangeActual.K
abbrev x : R0 := S2801E37X S2844D6F6BaseChangeActual.K
abbrev y : R0 := S2801E37Y S2844D6F6BaseChangeActual.K

/-- Actual factorization from order preserving: for any ring endomorphism φ of
R0 fixing x, (φ y - y)(φ y + y + 1) = 0. -/
theorem S3037_factorization (φ : R0 →+* R0) (hx : φ x = x) :
    (φ y - y) * (φ y + y + 1) = 0 := by
  have hrel : y ^ 2 + y = x ^ 3 - x := S2801E37_relation S2844D6F6BaseChangeActual.K
  have h := congrArg φ hrel
  simp only [map_add, map_pow, map_sub, hx] at h
  have h' : φ y ^ 2 + φ y = y ^ 2 + y := by rw [h, ← hrel]
  have hfac : (φ y - y) * (φ y + y + 1) = φ y ^ 2 + φ y - (y ^ 2 + y) := by ring
  rw [hfac, h']
  ring

#check S3037_factorization
#print axioms S3037_factorization

end LeanFormal.IUT.XiFPaper.S3037Factorization
end
