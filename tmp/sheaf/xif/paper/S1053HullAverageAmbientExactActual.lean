import tmp.sheaf.xif.paper.S1043CorrectedBridgeExactActual
import tmp.sheaf.xif.paper.S1037GlobalQPilotAuditActual
import tmp.sheaf.xif.paper.S994FiniteCarrierCor312Actual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual

/-! # S1053: hull-average identification via the ambient hull log

PaperSignedHull has the actual theorem
  signedHullLogVolume = -procession.average.
Hence the target average equality is exactly the ambient log identification.
This is the exact minimal ambient-hull identification; it is not a
definitional identity of the structure. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1053HullAverageAmbientExactActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S1037GlobalQPilotAuditActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory

universe uX uLabel
variable {l : PrimeGeFive}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (In : S994FiniteInput T)

def S1053AmbientHullLogExact : Prop :=
  (P.ambient.logVolume P.ambient.hull).toReal = -weightedPaperV (l := l) T (s994VS (l := l) T In)

def S1053SignedHullExact : Prop :=
  P.signedHullLogVolume = weightedPaperV (l := l) T (s994VS (l := l) T In)

theorem s1053HullAverage_iff_signed :
    P.procession.average = -weightedPaperV (l := l) T (s994VS (l := l) T In) ↔
      S1053SignedHullExact (l := l) P T In := by
  unfold S1053SignedHullExact
  rw [P.signedHullLogVolume_eq_neg_average]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    linarith

theorem s1053Signed_iff_ambient :
    S1053SignedHullExact (l := l) P T In ↔
      S1053AmbientHullLogExact (l := l) P T In := by
  unfold S1053SignedHullExact S1053AmbientHullLogExact
  rw [PaperSignedHull.signedHullLogVolume]
  exact neg_eq_iff_eq_neg

def S1053HullAverageExact : Prop :=
  P.procession.average = -weightedPaperV (l := l) T (s994VS (l := l) T In)

theorem s1053HullAverage_iff_ambient :
    S1053HullAverageExact (l := l) P T In ↔
      S1053AmbientHullLogExact (l := l) P T In :=
  (s1053HullAverage_iff_signed (l := l) P T In).trans (s1053Signed_iff_ambient (l := l) P T In)

theorem s1053HullAverage_of_ambient
    (h : S1053AmbientHullLogExact (l := l) P T In) :
    S1053HullAverageExact (l := l) P T In :=
  (s1053HullAverage_iff_ambient (l := l) P T In).mpr h

end LeanFormal.IUT.XiFPaper.S1053HullAverageAmbientExactActual

end
