import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual
import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual
import tmp.sheaf.xif.paper.PaperSignedHullSignedActual

/-! # S1132: ConcreteFinalScalarBridge (hull field + exact S1113 qPilot id)

The hull object is carried as the actual PaperSignedHull witness supplied by
the S1117/S1118 hull construction.  This file records the bridge and the exact
qPilot scalar identification; it does not fabricate the hull or the scalar
identification.  The heavy S1117/S1118 file is not imported here because its
transitive oleans are absent in the current build tree. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1132ConcreteFinalScalarBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.ThetaLinkLogKummerActual
open LeanFormal.IUT.XiFPaper.PaperSignedHullSignedActual
open MeasureTheory

universe ua uv upi umon ui uK uW u
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type uW}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)

/-- Exact S1113 qPilot scalar identification. -/
def S1132QPilotScalarIdentification : Prop :=
  I.qPilotSignedLogVolume = globalQVFamQPilotLog (l := l) T

/-- Concrete final scalar bridge: actual hull witness + qPilot component and
the exact source scalar identification. -/
structure ConcreteFinalScalarBridge where
  hull : PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value)
  hullComponent : Real
  hullComponent_eq : hullComponent = hull.procession.average
  qPilotComponent : Real
  qPilotComponent_eq : qPilotComponent = globalQVFamQPilotLog (l := l) T
  qPilot_source_eq : I.qPilotSignedLogVolume = qPilotComponent

/-- Exact hull side: an actual PaperSignedHull witness. -/
def S1132HullActualRequired : Prop :=
  Nonempty (PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value))

/-- Exact minimum: actual hull + S1113 qPilot scalar identification. -/
def S1132ExactMinimum : Prop :=
  S1132HullActualRequired places tuple ∧
    S1132QPilotScalarIdentification I T

/-- Bridge from an actual hull witness and the exact qPilot identification. -/
noncomputable def s1132ConcreteFinalScalarBridge
    (hull : PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value))
    (h : S1132QPilotScalarIdentification I T) :
    ConcreteFinalScalarBridge I T places tuple where
  hull := hull
  hullComponent := hull.procession.average
  hullComponent_eq := rfl
  qPilotComponent := globalQVFamQPilotLog (l := l) T
  qPilotComponent_eq := rfl
  qPilot_source_eq := h

/-- Bridge existence from the exact minimum. -/
theorem s1132Bridge_of_exactMinimum
    (h : S1132ExactMinimum I T places tuple) :
    Nonempty (ConcreteFinalScalarBridge I T places tuple) := by
  rcases h.1 with ⟨hull⟩
  exact ⟨s1132ConcreteFinalScalarBridge T places tuple hull h.2⟩

end LeanFormal.IUT.XiFPaper.S1132ConcreteFinalScalarBridgeActual
end