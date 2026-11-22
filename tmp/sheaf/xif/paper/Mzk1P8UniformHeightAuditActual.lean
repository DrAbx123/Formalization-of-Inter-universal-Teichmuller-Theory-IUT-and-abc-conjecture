/- P8 uniform-height audit: the exact remaining producer for P8UniformHeightBound
is the all-epsilon elliptic-height/Frey-height criterion; with the
ABCStatement -> ABCConjecture bridge it yields the P8 bound, and it feeds the
accepted P6 IV/display data into the P8 consumer. -/
import tmp.sheaf.xif.paper.Mzk1P8FromP6IVActual
import tmp.sheaf.xif.paper.Mzk1P6IVInequalityActual
import tmp.sheaf.xif.paper.Mzk1G1FreyHeightActual
import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

/-- Exact remaining P8 uniform-height producer: the all-epsilon elliptic
(Frey) height criterion. -/
abbrev P8UniformHeightProducer : Prop := ABCEllipticHeightCriterionAll

theorem p8UniformHeightProducer_iff_freyHeight :
    P8UniformHeightProducer ↔ ∀ ε : ℝ, 0 < ε → Nonempty (FreyHeightBound ε) :=
  freyHeightBoundAll_iff_criterionAll.symm

theorem p8UniformHeightProducer_implies_ABCStatement
    (h : P8UniformHeightProducer) : ABCStatement :=
  abcStatement_of_ellipticHeightCriterion h

/-- The remaining P8 bound from the producer plus the paper ABCStatement to
`ABCConjecture` bridge. -/
theorem p8UniformHeight_of_producer
    (h : P8UniformHeightProducer)
    (hbridge : ABCStatement → ABCConjecture) : P8UniformHeightBound :=
  (abcConjecture_iff_freyJProductHeightCriterion).mp
    (hbridge (p8UniformHeightProducer_implies_ABCStatement h))

/-- P8 consumer using the accepted P6 IV/display data and the remaining
uniform-height producer. -/
theorem p8_uniformHeight_remaining_consumer
    (A : ActualThm110Data) (c : ℝ) (D : P8FromP6IVData A c)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms)
    (h : P8UniformHeightProducer)
    (hbridge : ABCStatement → ABCConjecture) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) ∧
      ABCConjecture :=
  p8FromP6IV_combined A c D hCor312 (p8UniformHeight_of_producer h hbridge)

#print axioms p8UniformHeightProducer_iff_freyHeight
#print axioms p8UniformHeight_of_producer
#print axioms p8_uniformHeight_remaining_consumer

end LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightAuditActual
end
