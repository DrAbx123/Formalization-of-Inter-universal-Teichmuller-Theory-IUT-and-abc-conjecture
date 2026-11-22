import LeanFormal.IUT.IUTIII.Theorem311.SourceTheorem311ReferenceContract
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ContractSourceReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ParametricStepXI
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume

/-!
# C9-IUT bridge skeleton

This file is a typed skeleton only.  It does not construct a source output,
a q-pilot, or a hull: it records the actual project types that a future bridge
must consume.  There are no toy data types, no axioms, and no sorry.

The still-missing source bridge is represented explicitly by the proposition
C1SourceBridge, not assumed or proved.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure.C9IUTBridge

open scoped BigOperators
open Theorem311Source.SourceHodgeTheaterBridge

noncomputable section

universe u v w ua uv upi umon ui ux

/-- The explicit missing bridge proposition: the q-pilot log-volume is bounded
by the source hull log-volume.  This is intentionally only a Prop; the
skeleton neither proves nor assumes it. -/
def C1SourceBridge (qPilotLog : Real) (hullVolume : ENNReal) : Prop :=
  qPilotLog <= hullVolume.toReal

/-- Typed data for a future C9-IUT bridge.

The fields sourceOutput, qPilotLog, hull, and hullVolume are actual project
types.  The equalities tie them to the actual source declarations
absoluteDegreeNormalizedLowerSignedLog, sourceHolomorphicHull, and
sourceHullVolume.  The field c1SourceBridge is the explicit missing
proposition; it is not an axiom or a sorry. -/
structure C9IUTBridgeData
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (R : SourceTheorem311Realization.{u, v, w}
      l Label Choice)
    {V : Type uv}
    (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V)
    (Rimg : I.SourceImageRealization v)
    (n : Theorem311Source.OriginalInput.ThetaPilotCarrier l)
    {k : Type ux} [Field k] [NumberField k]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val) where
  sourceOutput : Theorem311Source.Theorem311Output R.input
  qPilotLog : Real
  qPilotLog_source :
    qPilotLog =
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters
  hull : Submonoid (I.ThetaPilotPoint v)
  hull_eq : hull = I.sourceHolomorphicHull v Rimg n
  hullVolume : ENNReal
  hullVolume_eq : hullVolume = I.sourceHullVolume v Rimg n
  c1SourceBridge : C1SourceBridge qPilotLog hullVolume

end

end LeanFormal.IUT.N8Closure.C9IUTBridge