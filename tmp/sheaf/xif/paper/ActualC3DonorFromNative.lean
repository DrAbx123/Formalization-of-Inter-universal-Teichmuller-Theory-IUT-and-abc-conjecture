import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.C3Roots
import tmp.sheaf.xif.paper.C3DonorFieldsFromSource
import tmp.sheaf.xif.paper.ThetaPacketQIdentificationActual

/-! # CONDITIONAL STATUS (xi-f)

Conditional on MissingC3DonorData. Native q lives at the F-completion while SourcePilotRegionDonors needs the Fmod base place; the base q/roots/kummer/tensor data are missing.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Actual C3 donor from native Q: construction status

The native q donor is actual:

  nativeQActual X : FinitePlaceQCandidate (nativeFPlaceOverBad X)

and nativeQDonorActual X is its Clause (b) Tate comparison witness.  The
source-theater theta packet has actual q = 1/5.

Obstacle: nativeQActual lives at the F-completion, while
SourcePilotRegionDonors.q must be a FinitePlaceQCandidate at the Fmod place

  nativeC3Place X : FinitePlaceAtPrime X.S.arithmetic.Fmod (nativeC3Prime X).

No restriction/descent map from the F-completion q to the Fmod completion is
available in the tree.  Therefore nativeQActual cannot fill the C3 donor q
field, and no SourcePilotRegionDonors is constructed here.

Actual data proved/constructed:
* nativeC3Prime and nativeC3Place (from C3DonorFieldsFromSource);
* sourceTheaterThetaPacket with q = 1/5;
* NativeC3Data (nativeQDonorActual X) L at the native F-place for an explicit
  native tensor landing donor L.

Exact missing object:
* MissingBaseQData: q at nativeC3Place with roots, kummerClass and rootChange;
* MissingBaseTensorLanding: tensorLanding at the base Fmod completion with the
  q-unit law for the base q;
* MissingC3DonorData: an OriginalInput with matching Fmod arithmetic plus the
  two base objects above.

No fake q, toy data, forbidden placeholder, axiom, or unfilled proof is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ActualC3DonorFromNative

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual native C3 rational prime. -/
abbrev actualC3Prime : Nat := nativeC3Prime X

/-- Actual native C3 base place (Fmod). -/
abbrev actualC3Place :
    FinitePlaceAtPrime X.S.arithmetic.Fmod (actualC3Prime X) :=
  nativeC3Place X

/-- The actual source-theater theta packet with q = 1/5. -/
noncomputable def sourceTheaterThetaPacket : FiniteThetaPacket l :=
  (sourceTheater l).thetaPacket

/-- The source-theater theta packet has actual q = 1/5. -/
theorem sourceTheaterThetaPacket_q :
    (sourceTheaterThetaPacket (l := l)).q = (5 : Real)⁻¹ := by
  unfold sourceTheaterThetaPacket
  exact sourceTheater_theta_q_eq (l := l)

/-- Actual native C3 data at the F-place, using nativeQDonorActual and an
explicit tensor landing donor L. -/
noncomputable def actualNativeC3Data
    (L : NativeTensorLandingDonor X) :
    NativeC3Data X (nativeQDonorActual X) :=
  nativeC3DataOfDonors X (nativeQDonorActual X) L

/-- The actual native q in that data is nativeQActual. -/
theorem actualNativeC3Data_q
    (L : NativeTensorLandingDonor X) :
    (actualNativeC3Data (X := X) L).q = nativeQActual X :=
  rfl

/-- Exact missing base-completion q data.  This is not nativeQActual: it is a
separate FinitePlaceQCandidate at the Fmod place, plus its roots and Kummer
towers. -/
structure MissingBaseQData where
  q : FinitePlaceQCandidate (nativeC3Place X).val
  roots : NatRootSystem
    (candidateUnits (nativeC3Place X) q)
  roots' : NatRootSystem
    (candidateUnits (nativeC3Place X) q)
  kummerClass : CyclotomicTower
    (CommonPrimeCompletion (nativeC3Place X))
  rootChange : CyclotomicTower
    (CommonPrimeCompletion (nativeC3Place X))
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

/-- Exact missing base tensor landing: the tensor block is L's block, but the
landing map is at the base Fmod completion and satisfies the q-unit law for the
base q. -/
structure MissingBaseTensorLanding
    (L : NativeTensorLandingDonor X) (Q : MissingBaseQData) where
  tensorLanding :
    CommonPrimeCompletion (nativeC3Place X) →
      ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple
  tensorLanding_q :
    tensorLanding (Q.q.q : CommonPrimeCompletion (nativeC3Place X)) =
      (L.tensorUnit : ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple)

/-- Exact missing object for constructing SourcePilotRegionDonors from native
data: an OriginalInput with matching Fmod arithmetic, the base q/roots data, and
the base tensor landing. -/
structure MissingC3DonorData
    (I : OriginalInput l V)
    (L : NativeTensorLandingDonor X) where
  arithmetic_fmod_eq : I.initial.arithmetic.Fmod = X.S.arithmetic.Fmod
  baseQ : MissingBaseQData
  baseTensor : MissingBaseTensorLanding L baseQ

/-- The exact construction obligation for SourcePilotRegionDonors from native
data.  No q or tensor map is supplied by the native q donor itself. -/
def ActualC3DonorFromNativeRequired
    (I : OriginalInput l V)
    (L : NativeTensorLandingDonor X) : Prop :=
  Nonempty (MissingC3DonorData I L)

end LeanFormal.IUT.XiFPaper.ActualC3DonorFromNative

end
