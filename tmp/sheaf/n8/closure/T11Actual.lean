import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.SourceThetaToIQ
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity

/-!
# T11 actual: completion construction, exact residual, C4 alignment

The completion candidate is built from C3 qUnit and the label's Gaussian
exponent.  It constructs a SourceThetaIQInterface without a free interface
inhabitant and discharges sourceThetaIQObligation with no sorry.

The qUnit candidate is n-independent and is not proved equal to the source real
theta value.  The exact missing source link is ThetaScalePacketIdentification.
C4 value-monoid alignment is at log-degree only; a full
ValueMonoidAt -> IQCarrier map remains ValueMonoidToIQObligation.

No True, arbitrary Type, or free interface is used.
-/

noncomputable section

namespace ABCBridge.N8.T11Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]

/-- Actual theta completion candidate: C3 qUnit raised to the label's Gaussian
exponent. -/
def thetaCompletionActual
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place :=
  ((C3.qUnit : (CommonPrimeCompletion
      (K := I.initial.arithmetic.Fmod) C3.place)ˣ) :
    CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place) ^
    (gaussExponent j.1).toNat

/-- The actual source theta scale at n,j. -/
def thetaScaleActual
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) : Real :=
  thetaScale (I := I) C3 n j

/-- thetaScaleActual is definitionally the source theta value. -/
theorem thetaScaleActual_eq_source
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    thetaScaleActual (I := I) C3 n j = I.thetaValueAt (n.1 : Int) 0 j :=
  rfl

/-- Actual interface built from the local qUnit completion construction. -/
def thetaIQInterfaceActual
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    SourceThetaIQInterface (I := I) C3 where
  thetaCompletion := thetaCompletionActual (I := I) C3
  thetaScale := fun n j => thetaScale (I := I) C3 n j
  thetaScale_eq := fun n j => rfl
  thetaImage := fun n j =>
    C3.tensorLanding (thetaCompletionActual (I := I) C3 n j)
  thetaImage_eq := fun n j => rfl

/-- The actual interface obligation is discharged by the qUnit construction,
with no sorry. -/
theorem sourceThetaIQObligation_actual
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    SourceThetaIQObligation (I := I) C3 :=
  ⟨thetaIQInterfaceActual (I := I) C3⟩

/-- Exact missing identification between the source real theta value and the C3
finite theta packet.  It is a Prop, not a free data field. -/
def ThetaScalePacketIdentification
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  ∀ (n : ThetaPilotCarrier l) (j : SignedLabel l.value),
    thetaScale (I := I) C3 n j = C3.thetaPacket.scale j

/-- Conditional compatibility: if the source/packet identification is supplied,
the real theta log is the Gaussian q-log. -/
theorem thetaScale_log_eq_gauss_of_packet
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (h : ThetaScalePacketIdentification (I := I) C3)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    Real.log (thetaScale (I := I) C3 n j) =
      (gaussExponent j.1).toNat * Real.log C3.thetaPacket.q := by
  rw [h n j]
  exact C3.thetaPacket.log_scale j

/-- The qUnit completion candidate is independent of the procession n.  The
actual source thetaScale is n-indexed; hence the qUnit candidate alone is not an
actual n-dependent source theta map. -/
theorem thetaCompletionActual_n_independent
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n n' : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    thetaCompletionActual (I := I) C3 n j =
      thetaCompletionActual (I := I) C3 n' j :=
  rfl

/-- Source degree-faithfulness at C4's C1 place. -/
def DegreeFaithful
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I Label) : Prop :=
  ∀ b : Real,
    I.logDegreeAt 0 0 C4.place.v
      (C4.place.R.posRealAction (Multiplicative.ofAdd b)) = b

/-- C4 value-monoid log-degree alignment: under degree faithfulness, the C4
thetaImageValue log-degree is log of T11 thetaScale. -/
theorem c4_logDegree_eq_log_thetaScale
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I Label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hdeg : DegreeFaithful (I := I) C4)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    I.logDegreeAt 0 0 C4.place.v (I.thetaImageValue C4.place.R n j) =
      Real.log (thetaScale (I := I) C3 n j) := by
  rw [I.thetaImageValue_eq_ofAdd_gauss C4.place.v C4.place.R n j]
  rw [hdeg]
  exact (log_thetaValueAt_eq_gauss (I := I) n j).symm

/-- A full C4 value-monoid -> IQ map remains an explicit obligation.  No
inhabitant is asserted and no arbitrary function is introduced. -/
structure ValueMonoidToIQMap
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I Label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : SourceThetaIQInterface (I := I) C3) where
  toIQ : I.ValueMonoidAt 0 0 C4.place.v → IQCarrier C3
  thetaImage_compat : ∀ (n : ThetaPilotCarrier l) (j : SignedLabel l.value),
    toIQ (I.thetaImageValue C4.place.R n j) = D.thetaImage n j

def ValueMonoidToIQObligation
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I Label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : SourceThetaIQInterface (I := I) C3) : Prop :=
  Nonempty (ValueMonoidToIQMap (I := I) C4 C3 D)

end ABCBridge.N8.T11Actual
