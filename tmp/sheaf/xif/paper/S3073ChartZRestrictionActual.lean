import tmp.sheaf.xif.paper.S3072ZSquareActual
import tmp.sheaf.xif.paper.S2809E6FiniteActual
import tmp.sheaf.xif.paper.S3054ProjectiveTransport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3072ZSquareActual
open LeanFormal.IUT.XiFPaper.S3071BranchFactorExtraction
open LeanFormal.IUT.XiFPaper.S3054ProjectiveTransport
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3073ChartZRestrictionActual

abbrev K2 := S3062ChartZPreservationProof.K

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

abbrev R2 := S2801E37CoordinateRing K2
abbrev G := S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K
abbrev ChartZ : S2801E37AffineScheme S2844D6F6BaseChangeActual.K ⟶ G :=
  S2820E37ChartZMap S2844D6F6BaseChangeActual.K

/-- Chart-Z restriction data extracted from z²=1 and z=Spec.map φ. -/
structure S3073ChartZRestriction
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X) where
  z : S2801E37AffineScheme K2 ⟶ S2801E37AffineScheme K2
  φ : R2 ≃+* R2
  hz : z = Spec.map (CommRingCat.ofHom φ.toRingHom)
  hφ2 : φ.toRingHom.comp φ.toRingHom = RingHom.id R2
  hsquare : ChartZ ≫ β.left = z ≫ ChartZ

/-- Actual: order-two ∞-fixing β gives chart-Z restriction data (z,φ,φ²,square). -/
theorem S3073_restriction_of_β
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (hfix : S3062InfinityFixed β) :
    Nonempty (S3073ChartZRestriction β) := by
  obtain ⟨z, hzsq, hsquare⟩ := S3072_zSquare β hβ hfix
  obtain ⟨φ, hz, hφ2⟩ := (S3071_zPhiData_of_square z hzsq).some
  exact ⟨⟨z, φ, hz, hφ2, hsquare⟩⟩

/-- K-linearity of the extracted φ. -/
def S3073PhiFixesK (φ : R2 ≃+* R2) : Prop :=
  ∀ a : K2,
    φ (Ideal.Quotient.mk (S2801E37Ideal K2) (MvPolynomial.C a)) =
      Ideal.Quotient.mk (S2801E37Ideal K2) (MvPolynomial.C a)

/-- φ fixes the X coordinate. -/
def S3073PhiFixesX (φ : R2 ≃+* R2) : Prop :=
  φ (S2801E37X K2) = S2801E37X K2

/-!
## Exact statements and first error

Actual:
* S3073ChartZRestriction: z, φ, hz, hφ2, chart-Z square;
* S3073_restriction_of_β: from β²=1 and S3062InfinityFixed β, actual extraction
  via S3072_zSquare + S3071_zPhiData_of_square.

First errors:
1. S3073PhiFixesK φ: needs β's Over/S2844Base structure-map compatibility to
   show the chart-Z affine endomorphism is over Spec K, hence φ fixes all
   S3030KMap a.  Not yet formalized.
2. S3073PhiFixesX φ: needs origin/∞-fixing to fix the chart-Z origin and then
   the X coordinate.  Not yet formalized.
3. Transport R2 → S3054 R0 (same ring, different hidden instance path) and
   S3054GluingData / S3061BranchFactor / S2888 classification not started.
No hk/hX/gluing/branch data is faked.
-/

#check S3073ChartZRestriction
#check S3073_restriction_of_β
#check S3073PhiFixesK
#check S3073PhiFixesX
#print axioms S3073_restriction_of_β

end LeanFormal.IUT.XiFPaper.S3073ChartZRestrictionActual
end
