/- P8 uniform height bound from the all-epsilon Frey producer, independent of
the producer-assembly wrapper. -/
import tmp.sheaf.xif.paper.ABCStatementBridgeActual
import tmp.sheaf.xif.paper.Mzk1G1FreyHeightActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import tmp.sheaf.xif.paper.Mzk1P8FromP6IVActual
import tmp.sheaf.xif.paper.Mzk1IVThm110Actual
import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightBoundProducerDoneActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.ABCStatementBridgeActual

abbrev P8FreyProducer : Prop := ∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε)
theorem p8FreyProducer_criterionAll (h : P8FreyProducer) :
    ABCEllipticHeightCriterionAll :=
  freyHeightBoundAll_iff_criterionAll.mp h
theorem p8FreyProducer_abcStatement (h : P8FreyProducer) : ABCStatement :=
  abcStatement_of_ellipticHeightCriterion (p8FreyProducer_criterionAll h)
theorem p8FreyProducer_ABCConjecture (h : P8FreyProducer) : ABCConjecture :=
  ABCStatementBridgeActual.abcStatement_to_ABCConjecture (p8FreyProducer_abcStatement h)
theorem p8FreyProducer_bound (h : P8FreyProducer) : P8UniformHeightBound :=
  p8UniformHeightBound_iff_abc.mpr (p8FreyProducer_ABCConjecture h)
theorem p8FreyProducer_combined
    (A : LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual.ActualThm110Data) (c : Real)
    (D : LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual.P8FromP6IVData A c)
    (hCor312 : LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.thm110Lhs A.toTerms ≤
      LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.thm110Mid A.toTerms +
      LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.thm110Cor312Gap A.toTerms)
    (h : P8FreyProducer) :
    LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.thm110Lhs
        (Mzk1P8ActualDisplayHeightActual.p8ActualDisplayTerms A) ≤
      LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.thm110Rhs
        (Mzk1P8ActualDisplayHeightActual.p8ActualDisplayTerms A) ∧ ABCConjecture :=
  LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual.p8FromP6IV_combined A c D hCor312
    (p8FreyProducer_bound h)

#print axioms p8FreyProducer_combined
#print axioms p8FreyProducer_ABCConjecture
#print axioms p8FreyProducer_bound
end LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightBoundProducerDoneActual
end
