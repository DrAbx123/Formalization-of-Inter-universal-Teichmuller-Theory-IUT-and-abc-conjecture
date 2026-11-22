import tmp.sheaf.xif.paper.S3075PhiFixesKActual
import tmp.sheaf.xif.paper.S3054ProjectiveTransport
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3075PhiFixesKActual
open LeanFormal.IUT.XiFPaper.S3074PhiFixesKActual
open LeanFormal.IUT.XiFPaper.S3073ChartZRestrictionActual
open LeanFormal.IUT.XiFPaper.S3054ProjectiveTransport
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0
namespace LeanFormal.IUT.XiFPaper.S3076ChartZRestrictionOfHXAdapted
abbrev K0 := LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual.K
abbrev R0 := LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual.S2801E37CoordinateRing K0
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field K0 := S2847A6.fieldF
local instance : NumberField K0 := S2847A6.numberFieldF
local instance : DecidableEq K0 := Classical.decEq _
local instance : CommRing R0 := Ideal.Quotient.commRing (LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual.S2801E37Ideal K0)
local instance : Algebra K0 R0 := RingHom.toAlgebra ((Ideal.Quotient.mk (LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual.S2801E37Ideal K0)).comp (MvPolynomial.C : K0 →+* MvPolynomial (Fin 2) K0))
theorem S3076_chartZRestriction_of_hX
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (hfix : S3062InfinityFixed β)
    (D : S3073ChartZRestriction β)
    (hX : D.φ (S2801E37X S3062ChartZPreservationProof.K) = S2801E37X S3062ChartZPreservationProof.K) :
    Nonempty (S3054ChartZRestriction β) := by
  let φ' : S3030AffineOriginClassification.R0 ≃+* S3030AffineOriginClassification.R0 := D.φ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact φ'
  · intro a
    have hk := S3075_phi_fixes_K β hβ hfix D a
    simpa [φ', S3030KMap, LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual.S2801E37X] using hk
  · simpa [φ'] using D.hφ2
  · simpa [φ'] using hX
  · have hs := D.hsquare
    rw [D.hz] at hs
    simpa [φ', S2820E37ChartZMap] using hs
#check S3076_chartZRestriction_of_hX
end LeanFormal.IUT.XiFPaper.S3076ChartZRestrictionOfHXAdapted
end
