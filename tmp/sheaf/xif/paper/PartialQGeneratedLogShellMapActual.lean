import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import tmp.sheaf.n8.closure.SourcePilotRegion

/-!
# Partial q-generated actual Kummer/log-shell map

IUT III, §1.5/§3: the Kummer/log-shell value layer contains the q-generated
submonoid acting on the local log-shell.

This file constructs the genuine partial actual map available from the source:

* qMon R C3 : ValueMonoidAt 0 0 v, the image of the actual C3 theta q-value
  under the actual SourceImageRealization.posRealAction;
* qGeneratedValueMap : Multiplicative Nat ->* ValueMonoidAt 0 0 v,
  n |-> qMon^n;
* qGeneratedCompletionMap : Multiplicative Nat ->* (CommonPrimeCompletion
  C3.place)^x, n |-> C3.qUnit^n, using the actual C3 qUnit.

Both maps are actual; unit and multiplication laws are proved.  The generator
identifications qGeneratedValueMap 1 = qMon and qGeneratedCompletionMap 1 =
C3.qUnit are proved.  This is explicitly the q-generated partial map, not a
total Mon v -> Completion map; no arbitrary total extension is asserted.

No inequality, no Missing-only structure, no donor, no toy/True/PUnit/axiom/
sorry.  WRITE-ONLY; no local compile; queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PartialQGeneratedLogShellMapActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual generator qMon in the local value monoid: the image of the
actual C3 theta q-value under the actual positive-real realization. -/
noncomputable def qMon
    (v : V) (R : I.SourceImageRealization v) :
    I.ValueMonoidAt 0 0 v :=
  R.posRealAction (Multiplicative.ofAdd (Real.log C3.thetaPacket.q))

/-- qMon is exactly the realization of the actual theta q-value. -/
theorem qMon_eq
    (v : V) (R : I.SourceImageRealization v) :
    qMon I C3 v R =
      R.posRealAction (Multiplicative.ofAdd (Real.log C3.thetaPacket.q)) := rfl

/-- The actual q-generated value submonoid map: n |-> qMon^n. -/
noncomputable def qGeneratedValueMap
    (v : V) (R : I.SourceImageRealization v) :
    Multiplicative Nat →* I.ValueMonoidAt 0 0 v where
  toFun n := qMon I C3 v R ^ n.toAdd
  map_one' := by simp
  map_mul' := by
    intro a b
    simp [pow_add]

/-- The actual q-generated completion map: n |-> qUnit^n. -/
noncomputable def qGeneratedCompletionMap :
    Multiplicative Nat →* (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place)ˣ where
  toFun n := C3.qUnit ^ n.toAdd
  map_one' := by simp
  map_mul' := by
    intro a b
    simp [pow_add]

/-- The value map sends the generator to qMon. -/
theorem qGeneratedValueMap_one
    (v : V) (R : I.SourceImageRealization v) :
    qGeneratedValueMap I C3 v R (Multiplicative.ofAdd 1) = qMon I C3 v R := by
  simp [qGeneratedValueMap]

/-- The completion map sends the generator to the actual C3 qUnit. -/
theorem qGeneratedCompletionMap_one :
    qGeneratedCompletionMap I C3 (Multiplicative.ofAdd 1) = C3.qUnit := by
  simp [qGeneratedCompletionMap]

/-- The value map preserves the unit. -/
theorem qGeneratedValueMap_one' (v : V) (R : I.SourceImageRealization v) :
    qGeneratedValueMap I C3 v R 1 = 1 :=
  map_one (qGeneratedValueMap I C3 v R)

/-- The value map preserves multiplication. -/
theorem qGeneratedValueMap_mul (v : V) (R : I.SourceImageRealization v)
    (a b : Multiplicative Nat) :
    qGeneratedValueMap I C3 v R (a * b) =
      qGeneratedValueMap I C3 v R a * qGeneratedValueMap I C3 v R b :=
  map_mul (qGeneratedValueMap I C3 v R) a b

/-- The completion map preserves the unit. -/
theorem qGeneratedCompletionMap_one' :
    qGeneratedCompletionMap I C3 1 = 1 :=
  map_one (qGeneratedCompletionMap I C3)

/-- The completion map preserves multiplication. -/
theorem qGeneratedCompletionMap_mul (a b : Multiplicative Nat) :
    qGeneratedCompletionMap I C3 (a * b) =
      qGeneratedCompletionMap I C3 a * qGeneratedCompletionMap I C3 b :=
  map_mul (qGeneratedCompletionMap I C3) a b

/-- The q-generated value image is the range of the value map. -/
def qGeneratedValueImage (v : V) (R : I.SourceImageRealization v) :
    Set (I.ValueMonoidAt 0 0 v) :=
  Set.range (qGeneratedValueMap I C3 v R)

/-- qMon lies in the q-generated value image. -/
theorem qMon_mem_qGeneratedValueImage
    (v : V) (R : I.SourceImageRealization v) :
    qMon I C3 v R ∈ qGeneratedValueImage I C3 v R :=
  ⟨Multiplicative.ofAdd 1, qGeneratedValueMap_one I C3 v R⟩

end LeanFormal.IUT.XiFPaper.PartialQGeneratedLogShellMapActual
