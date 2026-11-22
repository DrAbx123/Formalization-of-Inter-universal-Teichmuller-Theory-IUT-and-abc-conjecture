/- P8 producer assembly: the all-epsilon Frey-height producer implies ABC and
hence the P8 uniform height bound; combined with the accepted P6/IV display
data it gives the P8 consumer. -/
import tmp.sheaf.xif.paper.Mzk1P8FromP6IVActual
import tmp.sheaf.xif.paper.Mzk1G1FreyHeightActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1ABCStatementBridgeActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8ProducerAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCStatementBridgeActual

/-- Exact remaining P8 producer: Frey height data for every epsilon. -/
abbrev P8UniformHeightProducer : Prop := ∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε)

theorem p8Producer_iff_criterionAll :
    P8UniformHeightProducer ↔ ABCEllipticHeightCriterionAll :=
  freyHeightBoundAll_iff_criterionAll

theorem p8Producer_implies_abcStatement (h : P8UniformHeightProducer) :
    ABCStatement :=
  abcStatement_of_ellipticHeightCriterion (p8Producer_iff_criterionAll.mp h)

theorem p8Producer_implies_ABCConjecture (h : P8UniformHeightProducer) :
    ABCConjecture :=
  abcStatement_to_ABCConjecture (p8Producer_implies_abcStatement h)

theorem p8UniformHeightBound_of_producer (h : P8UniformHeightProducer) :
    P8UniformHeightBound :=
  p8UniformHeightBound_iff_abc.mpr (p8Producer_implies_ABCConjecture h)

theorem p8Producer_combined
    (A : ActualThm110Data) (c : Real) (D : P8FromP6IVData A c)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms)
    (h : P8UniformHeightProducer) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) ∧
      ABCConjecture :=
  p8FromP6IV_combined A c D hCor312 (p8UniformHeightBound_of_producer h)

#print axioms p8Producer_implies_ABCConjecture
#print axioms p8UniformHeightBound_of_producer
#print axioms p8Producer_combined

end LeanFormal.IUT.XiFPaper.P8ProducerAssemblyActual
end
