import tmp.sheaf.xif.paper.PartialQGeneratedLogShellMapActual
import tmp.sheaf.xif.paper.LiteralIQCarrierConstructionActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Theta-pilot q-image maps: actual value and completion images

Q3 intermediate data, built on the actual q-generated maps of
PartialQGeneratedLogShellMapActual.

For the actual Theta-pilot image index

  ThetaPilotImageIndex = ThetaPilotCarrier l * SignedLabel l.value,

the actual theta exponent is gaussExponent j. This gives two actual maps:

* thetaPilotValueImageMap : index -> ValueMonoidAt 0 0 v,
  j |-> qMon^(gaussExponent j);
* thetaPilotCompletionImageMap : index -> (CommonPrimeCompletion C3.place)^x,
  j |-> C3.qUnit^(gaussExponent j).

Their actual image sets are finite, and the completion image set is compact in
the actual normed completion. These are constructed from the actual q and the
actual theta exponents; no total Mon v -> Completion map is fabricated.

The remaining literal-IQ embedding from the actual completion image to
LiteralIQAmbient requires the D-/F-prime-strip capsule place comparison; it is
not replaced by an arbitrary map here.

No Missing-only structure, donor, True/PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ThetaPilotQImagePartialActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PartialQGeneratedLogShellMapActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual Theta-pilot image index: processions times signed labels. -/
abbrev ThetaPilotImageIndex : Type :=
  ThetaPilotCarrier l × SignedLabel l.value

/-- The actual theta exponent attached to a signed label. -/
def thetaImageExponent (idx : ThetaPilotImageIndex (l := l)) : Nat :=
  (gaussExponent idx.2.1).toNat

/-- The actual Theta-pilot value image map: qMon to the theta exponent. -/
noncomputable def thetaPilotValueImageMap
    (v : V) (R : I.SourceImageRealization v)
    (idx : ThetaPilotImageIndex (l := l)) :
    I.ValueMonoidAt 0 0 v :=
  qGeneratedValueMap I C3 v R
    (Multiplicative.ofAdd (thetaImageExponent (l := l) idx))

/-- The actual Theta-pilot completion image map: C3.qUnit to the theta
exponent. -/
noncomputable def thetaPilotCompletionImageMap
    (idx : ThetaPilotImageIndex (l := l)) :
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place)ˣ :=
  qGeneratedCompletionMap I C3
    (Multiplicative.ofAdd (thetaImageExponent (l := l) idx))

/-- The actual value image set of the Theta-pilot q-image. -/
def thetaPilotValueImageSet
    (v : V) (R : I.SourceImageRealization v) :
    Set (I.ValueMonoidAt 0 0 v) :=
  Set.range (thetaPilotValueImageMap (C3 := C3) v R)

/-- The actual completion image set of the Theta-pilot q-image. -/
def thetaPilotCompletionImageSet :
    Set ((CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place)ˣ) :=
  Set.range (thetaPilotCompletionImageMap (C3 := C3))

/-- The value image set is finite. -/
theorem thetaPilotValueImageSet_finite
    (v : V) (R : I.SourceImageRealization v) :
    (thetaPilotValueImageSet (C3 := C3) v R).Finite :=
  Set.finite_range _

/-- The completion image set is finite. -/
theorem thetaPilotCompletionImageSet_finite :
    (thetaPilotCompletionImageSet (C3 := C3)).Finite :=
  Set.finite_range _

/-- The completion image set is compact in the actual normed completion. -/
theorem thetaPilotCompletionImageSet_compact :
    IsCompact (thetaPilotCompletionImageSet (C3 := C3)) := by
  haveI : T2Space
      ((CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place)ˣ) :=
    inferInstance
  exact (thetaPilotCompletionImageSet_finite (C3 := C3)).isCompact

/-- The value image map is the actual q-generated map at the theta exponent. -/
theorem thetaPilotValueImageMap_eq
    (v : V) (R : I.SourceImageRealization v)
    (idx : ThetaPilotImageIndex (l := l)) :
    thetaPilotValueImageMap (C3 := C3) v R idx =
      qMon I C3 v R ^ thetaImageExponent (l := l) idx := by
  unfold thetaPilotValueImageMap qGeneratedValueMap thetaImageExponent
  simp

/-- The completion image map is the actual q-generated map at the theta
exponent. -/
theorem thetaPilotCompletionImageMap_eq
    (idx : ThetaPilotImageIndex (l := l)) :
    thetaPilotCompletionImageMap (C3 := C3) idx =
      C3.qUnit ^ thetaImageExponent (l := l) idx := by
  unfold thetaPilotCompletionImageMap qGeneratedCompletionMap
  simp

end LeanFormal.IUT.XiFPaper.ThetaPilotQImagePartialActual

end
