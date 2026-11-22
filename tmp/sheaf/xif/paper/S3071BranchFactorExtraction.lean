import tmp.sheaf.xif.paper.S3070HnonActual
import tmp.sheaf.xif.paper.S2809E6FiniteActual
import tmp.sheaf.xif.paper.S3055RingAutoOfChartZ
import tmp.sheaf.xif.paper.S3053UnconditionalAffineClassification
import tmp.sheaf.xif.paper.S2888OriginPreservingOrderTwo

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3070HnonActual
open LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ
open LeanFormal.IUT.XiFPaper.S3053UnconditionalAffineClassification
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S3061BranchFactorization
open LeanFormal.IUT.XiFPaper.S3058ChartZPreservation
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3071BranchFactorExtraction

abbrev K2 := S3062ChartZPreservationProof.K

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field K2 := S2847A6.fieldF
local instance : NumberField K2 := S2847A6.numberFieldF
local instance : DecidableEq K2 := Classical.decEq _

abbrev R2 := S2801E37CoordinateRing K2

/-- z²=1 for the chart-Z endomorphism. -/
def S3071ZSquare
    (z : S2801E37AffineScheme K2 ⟶ S2801E37AffineScheme K2) : Prop :=
  z ≫ z = 𝟙 (S2801E37AffineScheme K2)

/-- Extracted φ and its properties from a z with z²=1. -/
structure S3071ZPhiData
    (z : S2801E37AffineScheme K2 ⟶ S2801E37AffineScheme K2)
    (hzsq : S3071ZSquare z) where
  φ : R2 ≃+* R2
  hz : z = Spec.map (CommRingCat.ofHom φ.toRingHom)
  hφ2 : φ.toRingHom.comp φ.toRingHom = RingHom.id R2

/-- Actual: z²=1 gives a ring auto φ with z=Spec.map φ and φ²=1. -/
theorem S3071_zPhiData_of_square
    (z : S2801E37AffineScheme K2 ⟶ S2801E37AffineScheme K2)
    (hzsq : S3071ZSquare z) :
    Nonempty (S3071ZPhiData z hzsq) := by
  have hpre : Spec.preimage (z ≫ z) =
      Spec.preimage (𝟙 (S2801E37AffineScheme K2)) :=
    congrArg Spec.preimage hzsq
  rw [Spec.preimage_comp, Spec.preimage_id] at hpre
  have hcomp : (Spec.preimage z).hom.comp (Spec.preimage z).hom =
      RingHom.id R2 := by
    have := congrArg CommRingCat.Hom.hom hpre
    simpa using this
  let φRing : R2 →+* R2 := (Spec.preimage z).hom
  let φ : R2 ≃+* R2 := RingEquiv.ofRingHom φRing φRing hcomp hcomp
  have hφto : φ.toRingHom = φRing := rfl
  refine ⟨φ, ?_, ?_⟩
  · exact (Spec.map_preimage z).symm
  · change (Spec.preimage z).hom.comp (Spec.preimage z).hom = RingHom.id R2
    exact hcomp

/-!
## Exact statements and first error

Actual:
* S3071ZSquare: z ≫ z = 1.
* S3071ZPhiData: φ : R2 ≃+* R2, z = Spec.map φ, φ² = 1.
* S3071_zPhiData_of_square: given z and z²=1, actual extraction of φ
  (φ := Spec.preimage z, hz by Spec.map_preimage, hφ2 by
  Spec.preimage_comp + RingEquiv.ofRingHom).

First error:
S3071ZSquare z is not yet constructed from
hsquare : ChartZMap ≫ β.left = z ≫ ChartZMap and β²=1.  Route: cancel the
mono ChartZMap, use β.left ≫ β.left = (β ≫ β).left = 1; but β.left must be
typed as an endomorphism of E37ProjGluedScheme K2 e2 (the Over.left bridge),
so the associativity rewrite needs the explicit βs/hβs transport as in S3069.
No z², φ, hk, hX, or branch data is faked.
-/

#check S3071ZSquare
#check S3071ZPhiData
#check S3071_zPhiData_of_square
#print axioms S3071_zPhiData_of_square

end LeanFormal.IUT.XiFPaper.S3071BranchFactorExtraction
end
