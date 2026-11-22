import tmp.sheaf.xif.paper.GlobalThetaPilotIQValueTransportActualAdapted

/-!
# ValueMonoidAt -> completion: actual degree data and exact missing map

The actual source value monoid at a place is

  I.ValueMonoidAt 0 0 v = (I.primeStripAt 0 0).Mon v,

with the actual degree monoid homomorphism

  (I.primeStripAt 0 0).degree v : Mon v ->* Multiplicative Real.

This gives an actual real log-degree map

  valueMonoidLogDegree v : Mon v -> Real.

The required map for the global Theta-pilot value transport is a monoid map

  I.ValueMonoidAt 0 0 v ->* CommonPrimeCompletion (P.stripPlace v).

The source prime strip supplies no such completion-valued map: its value data are
the abstract monoid Mon v, its degree to Multiplicative Real, and the finite
place/completion objects separately.  The completion is not a quotient or a
target of the value monoid in the frozen source.

This file constructs the actual degree/log-degree data and records the exact
missing completion-valued monoid map.  No trivial monoid map to the completion is
inserted and no map is fabricated.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ValueMonoidToCompletionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotIQValueTransportActualAdapted

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]
variable (P : PrimeStripC3PlaceComparison (V := V) (I := I) C3)
variable (v : V)

/-- The actual degree monoid homomorphism of the source value monoid. -/
def valueMonoidDegree :
    I.ValueMonoidAt 0 0 v →* Multiplicative Real :=
  (I.primeStripAt 0 0).degree v

/-- The actual degree map is the source prime-strip degree. -/
theorem valueMonoidDegree_eq :
    valueMonoidDegree (I := I) v = (I.primeStripAt 0 0).degree v := rfl

/-- The actual real log-degree of a value-monoid element. -/
def valueMonoidLogDegree (x : I.ValueMonoidAt 0 0 v) : Real :=
  I.logDegreeAt 0 0 v x

/-- The log-degree is the additive form of the actual degree map. -/
theorem valueMonoidLogDegree_eq (x : I.ValueMonoidAt 0 0 v) :
    valueMonoidLogDegree (I := I) v x =
      Multiplicative.toAdd (valueMonoidDegree (I := I) v x) := rfl

/-- The actual degree map is multiplicative. -/
theorem valueMonoidLogDegree_mul (x y : I.ValueMonoidAt 0 0 v) :
    valueMonoidLogDegree (I := I) v (x * y) =
      valueMonoidLogDegree (I := I) v x + valueMonoidLogDegree (I := I) v y :=
  I.logDegreeAt_mul 0 0 v x y

/-- Exact missing source-compatible monoid map from the value monoid to the
completion at the aligned place. -/
structure ValueMonoidToCompletionMap where
  toCompletion : I.ValueMonoidAt 0 0 v →*
    CommonPrimeCompletion (P.stripPlace v)

/-- Exact missing object type for the completion-valued value map. -/
def ValueMonoidToCompletionObstruction : Prop :=
  Nonempty (ValueMonoidToCompletionMap (I := I) C3 P v)

/-- The obstruction is exactly the missing monoid map to the completion. -/
theorem ValueMonoidToCompletionObstruction_iff :
    ValueMonoidToCompletionObstruction (I := I) C3 P v ↔
      Nonempty (ValueMonoidToCompletionMap (I := I) C3 P v) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.ValueMonoidToCompletionActualAdapted

end