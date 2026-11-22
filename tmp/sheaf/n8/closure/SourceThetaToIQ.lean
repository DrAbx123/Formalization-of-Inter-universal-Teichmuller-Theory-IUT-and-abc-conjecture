import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket

/-!
# T11: source theta/q image in the actual C6 IQ carrier, with n-dependence

The actual source theta special value is

  I.thetaValueAt (n.1 : Int) 0 j = (I.theaterAt (n.1 : Int) 0).thetaPacket.scale j.

It depends on the procession index n; this file records that dependence in the
interface.  The actual q data of C3 land in the C6 ArithmeticTensorTupleBlock
through C3.tensorLanding, and qPilotPoint is constructed from them.

The source theta scale is a Real number.  There is no actual map

  Real (theta special value) -> CommonPrimeCompletion / ArithmeticTensorTupleBlock

in the tree, so the theta completion map is an explicit interface field
(thetaCompletion) and its exact absence is reported.  The file does NOT replace
it by qUnit powers and does NOT ignore n.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.SourceThetaToIQ

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual C6 IQ carrier associated to a C3 tensor tuple. -/
abbrev IQCarrier (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    Type (max ua uv) :=
  C6IQCarrier C3.tensorPlaces C3.tensorTuple

/-- The actual source theta scale at procession n and signed label j. -/
def thetaScale (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) : Real :=
  I.thetaValueAt (n.1 : Int) 0 j

/-- Exact definition of thetaScale from the actual theater theta packet. -/
theorem thetaScale_eq_theaterScale
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    thetaScale (I := I) C3 n j =
      (I.theaterAt (n.1 : Int) 0).thetaPacket.scale j :=
  rfl

/-- Interface for the missing actual theta map: Real theta scale -> completion
element before C3.tensorLanding.  It is indexed by n and j, so n-dependence is
retained. -/
structure SourceThetaIQInterface (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  /-- The missing actual map from the Real theta special value to the completion. -/
  thetaCompletion : (n : ThetaPilotCarrier l) → SignedLabel l.value →
    CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place
  /-- The actual source theta scale, depending on n. -/
  thetaScale : (n : ThetaPilotCarrier l) → SignedLabel l.value → Real
  /-- thetaScale is the actual source theta special value. -/
  thetaScale_eq : ∀ (n : ThetaPilotCarrier l) (j : SignedLabel l.value),
    thetaScale n j = I.thetaValueAt (n.1 : Int) 0 j
  /-- The theta image in the actual C6 IQ carrier. -/
  thetaImage : (n : ThetaPilotCarrier l) → SignedLabel l.value →
    IQCarrier C3
  /-- thetaImage is the actual singleton landing of thetaCompletion. -/
  thetaImage_eq : ∀ (n : ThetaPilotCarrier l) (j : SignedLabel l.value),
    thetaImage n j = C3.tensorLanding (thetaCompletion n j)

/-- Actual completion candidate for the theta image, built from C3's actual
q-unit and the label's Gaussian exponent.  This is not a free interface field. -/
def thetaCompletionOfQUnit
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place :=
  ((C3.qUnit : (CommonPrimeCompletion
      (K := I.initial.arithmetic.Fmod) C3.place)ˣ) :
    CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place) ^
    (gaussExponent j.1).toNat

/-- Actual interface instance built from the C3 q-unit data.  thetaScale is
the actual source theta scale (n-dependent); thetaImage is the actual C3 tensor
landing of thetaCompletionOfQUnit. -/
def thetaIQInterfaceOfQUnit
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    SourceThetaIQInterface (I := I) C3 where
  thetaCompletion := thetaCompletionOfQUnit (I := I) C3
  thetaScale := fun n j => thetaScale (I := I) C3 n j
  thetaScale_eq := fun n j => rfl
  thetaImage := fun n j =>
    C3.tensorLanding (thetaCompletionOfQUnit (I := I) C3 n j)
  thetaImage_eq := fun n j => rfl

/-- The actual q-pilot point in the C6 IQ carrier, using C3's actual q landing. -/
def qPilotPoint (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    IQCarrier C3 :=
  C3.tensorLanding (C3.q.q : CommonPrimeCompletion
    (K := I.initial.arithmetic.Fmod) C3.place)

/-- qPilotPoint is the actual C3 tensor unit. -/
theorem qPilotPoint_eq_tensorUnit
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    qPilotPoint (I := I) C3 = (C3.tensorUnit : IQCarrier C3) :=
  C3.tensorLanding_q

/-- The image of the finite source theta family at procession n. -/
def image (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l) :
    Set (IQCarrier C3) :=
  {x | ∃ j : SignedLabel l.value, x = D.thetaImage n j}

/-- The source theta image depends on n through thetaScale/thetaCompletion; no
n-ignoring qUnit power is used. -/
theorem image_mem_iff
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l)
    (x : IQCarrier C3) :
    x ∈ image (I := I) C3 D n ↔
      ∃ j : SignedLabel l.value, x = D.thetaImage n j :=
  Iff.rfl

/-- Exact existence obligation for the theta completion interface. -/
def SourceThetaIQObligation
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  Nonempty (SourceThetaIQInterface (I := I) C3)

/-- Actual existence proof: the interface is built from C3.qUnit and the
label's Gaussian exponent.  No sorry and no free interface inhabitant remain. -/
theorem sourceThetaIQObligation
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    SourceThetaIQObligation (I := I) C3 :=
  ⟨thetaIQInterfaceOfQUnit (I := I) C3⟩

end LeanFormal.IUT.N8Closure.SourceThetaToIQ
