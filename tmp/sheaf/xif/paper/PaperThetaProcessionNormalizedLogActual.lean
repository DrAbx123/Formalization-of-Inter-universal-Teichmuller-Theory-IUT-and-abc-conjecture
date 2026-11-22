import tmp.sheaf.xif.paper.PaperThetaSideObjectActual
import tmp.sheaf.xif.paper.S301GlobalThetaHullLogActual
import tmp.sheaf.xif.paper.BadPlacePaperConstantsActual

-- S310: final unconditional procession normalization of the ThetaSideObject
-- hull log.  The per-b final log is thetaSideObject.hullLog directly; S301 is
-- auxiliary/diagnostic only and no conditional equality is part of the final object.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.PaperThetaProcessionNormalizedLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperThetaSideObjectActual
open LeanFormal.IUT.XiFPaper.S301GlobalThetaHullLogActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

-- Final per-b Theta log: directly the qside ThetaSideObject hullLog.
noncomputable def thetaSidePerBLog : Real :=
  (thetaSideObject (l := l) T b).hullLog

-- Final global Theta procession-normalized log.
noncomputable def thetaSideGlobalProcessionNormalizedLog : Real :=
  productProcessionFactor (l := l) *
    ∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b * thetaSidePerBLog (l := l) T b

theorem thetaSideGlobalProcessionNormalizedLog_formula :
    thetaSideGlobalProcessionNormalizedLog (l := l) T =
      productProcessionFactor (l := l) *
        ∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * (thetaSideObject (l := l) T b).hullLog := rfl

-- Final procession-normalized global root coefficient, directly weighted.
noncomputable def thetaSideGlobalProcessionRootCoefficient : Real :=
  productProcessionFactor (l := l) *
    ∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b * qVFamPaperRootCoefficient T b

theorem thetaSideGlobalProcessionRootCoefficient_formula :
    thetaSideGlobalProcessionRootCoefficient (l := l) T =
      productProcessionFactor (l := l) *
        ∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * qVFamPaperRootCoefficient T b := rfl

-- Auxiliary diagnostic only: unconditional identification with the S301
-- coefficient sum (definitional, no hypothesis and not part of the final object).
theorem thetaSideGlobalProcessionRootCoefficient_aux_s301 :
    thetaSideGlobalProcessionRootCoefficient (l := l) T =
      productProcessionFactor (l := l) *
        globalSourceHullS13RootCoefficient (l := l) T := by
  unfold thetaSideGlobalProcessionRootCoefficient
  congr 1

structure ThetaProcessionNormalizedLogObject where
  perBLog : Bad (nativePlaceSelection T) → Real
  perBLog_eq : perBLog = thetaSidePerBLog (l := l) T
  globalLog : Real
  globalLog_eq :
    globalLog = thetaSideGlobalProcessionNormalizedLog (l := l) T
  globalLog_formula :
    globalLog =
      productProcessionFactor (l := l) *
        ∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * (thetaSideObject (l := l) T b).hullLog
  rootCoefficient : Real
  rootCoefficient_eq :
    rootCoefficient = thetaSideGlobalProcessionRootCoefficient (l := l) T
  rootCoefficient_formula :
    rootCoefficient =
      productProcessionFactor (l := l) *
        ∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * qVFamPaperRootCoefficient T b

noncomputable def thetaProcessionNormalizedLogObject :
    ThetaProcessionNormalizedLogObject T where
  perBLog := thetaSidePerBLog (l := l) T
  perBLog_eq := rfl
  globalLog := thetaSideGlobalProcessionNormalizedLog (l := l) T
  globalLog_eq := rfl
  globalLog_formula := thetaSideGlobalProcessionNormalizedLog_formula (l := l) T
  rootCoefficient := thetaSideGlobalProcessionRootCoefficient (l := l) T
  rootCoefficient_eq := rfl
  rootCoefficient_formula :=
    thetaSideGlobalProcessionRootCoefficient_formula (l := l) T

#check thetaSidePerBLog
#check thetaSideGlobalProcessionNormalizedLog
#check thetaSideGlobalProcessionRootCoefficient
#check thetaSideGlobalProcessionRootCoefficient_aux_s301
#check thetaProcessionNormalizedLogObject

end LeanFormal.IUT.XiFPaper.PaperThetaProcessionNormalizedLogActual

end