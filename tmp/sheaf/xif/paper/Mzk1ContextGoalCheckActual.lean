import tmp.sheaf.xif.paper.Mzk1ActualRamifiedDataActual
import tmp.sheaf.xif.paper.Mzk1IVThm110Actual
import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import tmp.sheaf.xif.paper.Mzk1Cor312ToABCConsumerActual
import tmp.sheaf.xif.paper.Mzk1ThetaUnitLatticeBoundActual
import tmp.sheaf.xif.paper.Mzk1GaloisCompletionActual
import tmp.sheaf.xif.paper.Mzk1PadicFieldValuedQpActual

/-!
# Context goal check file

Diagnostic only: this file does not prove the target. It checks that the current
conditional target interfaces and key donor bridges exist and prints their axioms.
All compilation must go through the watchdog.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ContextGoalCheckActual

open LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ToABCConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaUnitLatticeBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1GaloisCompletionActual
open LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedQpActual

-- 3.12 conditional target
#check @LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual.actual_paper312
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual.actual_paper312

-- IV Thm 1.10 conditional display
#check @LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual.thm110_display_of_hCor312
#print axioms LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual.thm110_display_of_hCor312

-- hSlack derived interface
#check @LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.Thm110DisplayInputsOfCor312
#print axioms LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.Thm110DisplayInputsOfCor312

-- abc conditional consumer
#check @LeanFormal.IUT.XiFPaper.Mzk1Cor312ToABCConsumerActual.abcConjecture_of_namedInputs
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312ToABCConsumerActual.abcConjecture_of_namedInputs

-- hθ unit-lattice one-way bound
#check @LeanFormal.IUT.XiFPaper.Mzk1ThetaUnitLatticeBoundActual.unitLatticeLogVolume_le_thetaHull
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ThetaUnitLatticeBoundActual.unitLatticeLogVolume_le_thetaHull

-- stage4 withValMovedSigma val equality (stable green declaration)
#check @LeanFormal.IUT.XiFPaper.Mzk1GaloisCompletionActual.withValMovedSigma_val_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GaloisCompletionActual.withValMovedSigma_val_eq

-- Qp valuation normalization
#check @LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedQpActual.padicField_v_eq_valuation
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedQpActual.padicField_v_eq_valuation

end LeanFormal.IUT.XiFPaper.Mzk1ContextGoalCheckActual
