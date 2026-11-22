import tmp.sheaf.xif.paper.S900PerBThetaHullLogNonzeroActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual

/-! # S1065: audit of the old qPilotPaperRegion path (INVALID AS PAPER)

S1051/S1055 build the paper qPilot from qPilotPaperRegion.  But
qPilotPaperRegion is the theta j=1 region with paperRootCoefficientFamily
(cRoot = c_norm/(2l)), not the qPilot normalized region with c_norm (order).
S900 proves paperRootThetaHullNonzero = qPilotPaperRegion, so on the old path
the qPilot object coincides with the theta hull, q = theta.

Correct paper qPilot region is qPilotNormRegion = F(c_norm).  The exact
identification qPilotPaperRegion = qPilotNormRegion is recorded as a
proposition; no fake equality is asserted.  The old files are NOT deleted;
this audit marks them INVALID AS PAPER. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1065OldPathQPilotAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S900PerBThetaHullLogNonzeroActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- qPilotPaperRegion is the theta j=1 region at cRoot. -/
theorem s1065QPaperRegion_eq_thetaJ1 :
    qPilotPaperRegion (l := l) T b =
      rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily (l := l) T b) (oneLabel l) :=
  qPilotPaperRegion_eq_rootThetaRegion_one (l := l) T b

/-- S900: the nonzero theta hull is exactly qPilotPaperRegion. -/
theorem s1065ThetaHull_eq_qPaperRegion :
    paperRootThetaHullNonzero (l := l) T b =
      qPilotPaperRegion (l := l) T b :=
  paperRootThetaHullNonzero_eq_qPilotPaperRegion (l := l) T b

/-- Consequently the old qPilot region is the theta hull: q = theta. -/
theorem s1065QPaperRegion_eq_thetaHull :
    qPilotPaperRegion (l := l) T b =
      paperRootThetaHullNonzero (l := l) T b :=
  (s1065ThetaHull_eq_qPaperRegion (l := l) T b).symm

/-- The classical correct qPilot region F(c_norm) (order coefficient). -/
abbrev s1065CorrectQPilotRegion : Set (qVFamTensorBlock T b) :=
  qPilotNormRegion (l := l) T b

/-- Exact identification required to equate the old theta region with the
correct c_norm qPilot region.  This is NOT proved and is the precise gap. -/
def S1065QPaperRegion_eq_NormRegion : Prop :=
  qPilotPaperRegion (l := l) T b = qPilotNormRegion (l := l) T b

/-- The old path's object is the theta hull (S900), not the c_norm qPilot. -/
def S1065OldPathUsesTheta : Prop :=
  qPilotPaperRegion (l := l) T b =
    paperRootThetaHullNonzero (l := l) T b

theorem s1065OldPathUsesTheta_actual :
    S1065OldPathUsesTheta (l := l) T b :=
  s1065QPaperRegion_eq_thetaHull (l := l) T b

end LeanFormal.IUT.XiFPaper.S1065OldPathQPilotAuditActual

end
