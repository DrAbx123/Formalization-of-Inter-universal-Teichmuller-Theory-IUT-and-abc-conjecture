import tmp.sheaf.xif.paper.ThetaPilotObjectActual
import LeanFormal.IUT.Foundations.Theta.GaussianKernel

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Global Theta-pilot possible images from the actual bad places

This file constructs the actual global value-group images of the Theta-pilot
object at the bad places V_bad of the source initial-Theta data.

For each bad place b, the actual source q-parameter is
  q_b = I.initial.reduction.qParameter b;
the actual theta value at the signed label j is q_b^(gaussExponent j).
The global geometric candidate is the dependent value-group point

  b |-> Multiplicative.ofAdd (log (q_b^(gaussExponent j)))

in the product of the actual local value groups. The possible-image set is the
range over the finite signed labels. No sum over bad places is taken, and no
holomorphic hull is asserted: the hull construction is a separate layer.

The actual source strip anchor is recorded separately: the F-prime-strip
I.primeStripAt 0 0. The map from bad places to strip places is not fabricated.

No True/PUnit, empty type, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotPossibleImagesActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual bad-place q parameter. -/
def badQParameter (b : I.initial.badPlaces) : Real :=
  I.initial.reduction.qParameter b

/-- The actual local theta value at a bad place and signed label. -/
def badThetaValue (b : I.initial.badPlaces) (j : SignedLabel l.value) : Real :=
  (badQParameter (I := I) b) ^ (gaussExponent j.1).toNat

/-- The actual global local-value candidate for one signed label: the product
value-group point over the bad places. -/
def globalThetaPilotCandidate (j : SignedLabel l.value) :
    (b : I.initial.badPlaces) → Multiplicative Real :=
  fun b => Multiplicative.ofAdd (Real.log (badThetaValue (I := I) b j))

/-- The actual global possible-image set of the Theta-pilot object: the range
of the signed-label candidates in the product of the actual bad-place value
groups. This is a genuine set of local value-group points, not a raw log sum. -/
def globalThetaPilotPossibleImages :
    Set ((b : I.initial.badPlaces) → Multiplicative Real) :=
  Set.range (globalThetaPilotCandidate (I := I))

/-- The actual source F-prime-strip anchor at the Theta-pilot level. -/
abbrev globalThetaPilotStrip : FPrimeStrip V :=
  I.primeStripAt 0 0

/-- The global candidate set is finite. -/
theorem globalThetaPilotPossibleImages_finite :
    (globalThetaPilotPossibleImages (I := I)).Finite :=
  Set.finite_range _

/-- The global candidate set is compact in the product of the actual
bad-place value groups. -/
theorem globalThetaPilotPossibleImages_compact :
    IsCompact (globalThetaPilotPossibleImages (I := I)) := by
  haveI : T2Space ((b : I.initial.badPlaces) → Multiplicative Real) :=
    inferInstance
  exact (globalThetaPilotPossibleImages_finite (I := I)).isCompact

/-- Membership in the global possible-image set. -/
theorem mem_globalThetaPilotPossibleImages_iff
    (x : (b : I.initial.badPlaces) → Multiplicative Real) :
    x ∈ globalThetaPilotPossibleImages (I := I) ↔
      ∃ j : SignedLabel l.value,
        x = globalThetaPilotCandidate (I := I) j :=
  Iff.rfl

/-- The actual strip anchor is the source (0,0) F-prime-strip. -/
theorem globalThetaPilotStrip_eq :
    globalThetaPilotStrip (I := I) = I.primeStripAt 0 0 :=
  rfl

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotPossibleImagesActualAdapted

end
