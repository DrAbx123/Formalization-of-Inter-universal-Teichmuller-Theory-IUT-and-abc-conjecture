import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.xif.paper.PaperSignedHullSignedActual
import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1119ConcreteFinalScalarBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperSignedHullSignedActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual

universe ua uv upi umon ui uK uW
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type uW}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)

/-- Exact qPilot scalar identification from S1113. -/
def S1119QPilotScalarIdentification : Prop :=
  I.qPilotSignedLogVolume = globalQVFamQPilotLog (l := l) T

/-- Concrete final scalar bridge: actual hull object (supplied), its actual
signed procession component, and the exact qPilot scalar identification. -/
structure ConcreteFinalScalarBridge where
  hull : PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value)
  hullComponent : Real
  hullComponent_eq : hullComponent = hull.procession.average
  qPilotComponent : Real
  qPilotComponent_eq : qPilotComponent = globalQVFamQPilotLog (l := l) T
  qPilot_source_eq : I.qPilotSignedLogVolume = qPilotComponent

/-- Actual conditional construction: given an actual concrete hull and the
exact qPilot scalar identification, build the bridge. -/
noncomputable def concreteFinalScalarBridge
    (hull : PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value))
    (h : S1119QPilotScalarIdentification (l := l) (I := I) T) :
    ConcreteFinalScalarBridge (l := l) (I := I) T places tuple where
  hull := hull
  hullComponent := hull.procession.average
  hullComponent_eq := rfl
  qPilotComponent := globalQVFamQPilotLog (l := l) T
  qPilotComponent_eq := rfl
  qPilot_source_eq := h

/-- Exact hull-component condition: existence of the actual concrete hull. -/
def S1119HullComponentActualRequired : Prop :=
  Nonempty (PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value))

/-- Exact minimum: actual concrete hull plus exact qPilot identification. -/
def S1119ExactMinimum : Prop :=
  S1119HullComponentActualRequired (l := l) (I := I) places tuple ∧
    S1119QPilotScalarIdentification (l := l) (I := I) T

/-- Conditional exact construction from the exact minimum. -/
theorem concreteFinalScalarBridge_of_exact
    (h : S1119ExactMinimum (l := l) (I := I) T places tuple) :
    Nonempty (ConcreteFinalScalarBridge (l := l) (I := I) T places tuple) := by
  rcases h.1 with ⟨hull⟩
  exact ⟨concreteFinalScalarBridge (l := l) (I := I) T places tuple hull h.2⟩

end LeanFormal.IUT.XiFPaper.S1119ConcreteFinalScalarBridgeActual

end
