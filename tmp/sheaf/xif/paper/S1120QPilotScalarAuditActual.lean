import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual
import tmp.sheaf.xif.paper.GlobalQPilotObjectActual
import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual
import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1120QPilotScalarAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.GlobalQPilotObjectActual
open LeanFormal.IUT.XiFPaper.ThetaLinkLogKummerActual
open MeasureTheory

universe ua uv upi umon ui u
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- S1113's scalar identification. -/
def S1120OriginalIdentification : Prop :=
  I.qPilotSignedLogVolume = globalQVFamQPilotLog (l := l) T

/-- Actual global source q-pilot scalar is the bad-q abs-log total, not the
single local one-column q. -/
theorem s1120SourceGlobal_eq :
    sourceQPilotSignedLog I.initial = globalQPilotSignedLog I :=
  (globalQPilotSignedLog_eq_sourceQPilotSignedLog I).symm

/-- Exact local/global source identification: the single one-column qPilot scalar
must equal the actual global bad-q source scalar. -/
def S1120LocalSourceIdentification : Prop :=
  I.qPilotSignedLogVolume = sourceQPilotSignedLog I.initial

/-- Exact weighted qVFam normalization: the actual global bad-q source scalar
must equal the qVFamily weighted local normalized sum. -/
def S1120WeightedQVFamIdentification : Prop :=
  sourceQPilotSignedLog I.initial = globalQVFamQPilotLog (l := l) T

/-- Exact minimum for S1113: local source identification plus weighted qVFam
normalization.  The local/global source step is not implied by the weighted
normalization. -/
def S1120ExactMinimum : Prop :=
  S1120LocalSourceIdentification (I := I) ∧
    S1120WeightedQVFamIdentification (l := l) (I := I) T

theorem s1120Original_of_exactMinimum
    (h : S1120ExactMinimum (l := l) (I := I) T) :
    S1120OriginalIdentification (l := l) (I := I) T := by
  unfold S1120OriginalIdentification S1120ExactMinimum
    S1120LocalSourceIdentification S1120WeightedQVFamIdentification at *
  exact h.1.trans h.2

/-- Factorized equivalent form of S1113: existence of the actual global source
scalar as an intermediate. -/
theorem s1120Original_iff_exists_global :
    S1120OriginalIdentification (l := l) (I := I) T ↔
      ∃ mid : Real,
        I.qPilotSignedLogVolume = mid ∧
          mid = globalQVFamQPilotLog (l := l) T := by
  constructor
  · intro h
    exact ⟨I.qPilotSignedLogVolume, rfl, h⟩
  · rintro ⟨mid, h1, h2⟩
    exact h1.trans h2

end LeanFormal.IUT.XiFPaper.S1120QPilotScalarAuditActual

end
