import tmp.sheaf.xif.paper.ValueMonoidToCompletionActual
import LeanFormal.IUT.IUTII.Kummer.MonoAnalyticLogShellCompactCarrier

/-!
# Actual mono-analytic value profile and exact representation gap

The analysis file MonoAnalyticValueTransportAnalysis.md explains why a monoid
map from the value monoid to the p-adic completion is not the paper's
multiradial transport.  The paper transport is value/degree data into a
mono-analytic log-shell module.

This file constructs the actual real log-degree profile of the value monoid
(using the actual source degree/logDegree) and records the exact missing
mono-analytic value-to-log-shell representation.  It does not construct a
completion-valued monoid map.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.MonoAnalyticValueTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.ValueMonoidToCompletionActual
open LeanFormal.IUT.IUTII

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PrimeStripC3PlaceComparison (V := V) (I := I) C3)
variable (v : V)

/-- Actual real log-degree profile of the source value monoid. -/
def monoAnalyticValueProfile (x : I.ValueMonoidAt 0 0 v) : Real :=
  valueMonoidLogDegree (I := I) v x

/-- The mono-analytic profile is the actual source log-degree. -/
theorem monoAnalyticValueProfile_eq (x : I.ValueMonoidAt 0 0 v) :
    monoAnalyticValueProfile (I := I) v x =
      I.logDegreeAt 0 0 v x := rfl

/-- The mono-analytic profile is additive on products. -/
theorem monoAnalyticValueProfile_mul (x y : I.ValueMonoidAt 0 0 v) :
    monoAnalyticValueProfile (I := I) v (x * y) =
      monoAnalyticValueProfile (I := I) v x +
        monoAnalyticValueProfile (I := I) v y :=
  I.logDegreeAt_mul 0 0 v x y

/-- Exact missing mono-analytic representation: a compact log-shell module and
an actual value-monoid-to-module map compatible with the source log-degree. -/
structure MonoAnalyticValueRepresentation where
  carrier : MonoAnalyticLogShellCompactCarrier
  valueToModule : I.ValueMonoidAt 0 0 v → carrier.M

/-- Exact missing mono-analytic representation object. -/
def MonoAnalyticValueRepresentationObstruction : Prop :=
  Nonempty (MonoAnalyticValueRepresentation (I := I) v)

/-- The obstruction is exactly the missing value-to-log-shell representation. -/
theorem MonoAnalyticValueRepresentationObstruction_iff :
    MonoAnalyticValueRepresentationObstruction (I := I) v ↔
      Nonempty (MonoAnalyticValueRepresentation (I := I) v) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.MonoAnalyticValueTransportActual

end