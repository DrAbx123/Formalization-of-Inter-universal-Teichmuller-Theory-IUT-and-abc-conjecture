import tmp.sheaf.n8.closure.N8NativeClosure
import tmp.sheaf.n8.closure.C10BridgeProof
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction

/-!
# R49 C10 donor search

Search result (production):

1. SourceDefinition31Data constructors:
   - StageConstructionTrace.toSource (SourceDefinition31RootLemmas:3807) needs a
     StageConstructionTrace input; no concrete stage trace is produced from
     SourceNativeInitialThetaData.
   - sourceHaarActualOriginalInput (SourceUnitRegionHaarDataActual:348) needs an
     already supplied SourceDefinition31Data S; it does not construct S.
   So there is no production function
     SourceNativeInitialThetaData -> SourceDefinition31Data.

2. Native/contract bridge: SourceDefinition31NativeContractBridgeReduction
   exposes NativeContractRecordBridge and SourceContractRootSupply as Props
   (existential/equivalence gates), and ofNative only builds a partition
   fragment.  They do not supply a contract record.

3. OriginalInput index_equiv: the only concrete OriginalInput is
   sourceHaarActualOriginalInput S with V = Unit and index_equiv refl; it is
   not the native theater family and does not provide an equivalence
   X.family.index ≃ Int × Int.

4. Old C1 placeEquiv/R/fiber:
   - NativeC1.nativePlaceIndexEquiv supplies the native place bijection
     NativePlaces X.S ≃ NumberFieldPlaceIndex.
   - NativeC1.badPlace supplies a selected native place.
   - No SourceImageRealization selected donor exists for the native selected
     place (sourceHaarActualImageRealization only covers V = Unit, q = 1).
   - No fiberMonEquiv donor exists in production.
   In production there is no SourcePlaceRealization or SourceInputBinding
   declaration at all; those are tmp C1 interface types.

No arbitrary V and no arbitrary selected R are introduced.  The only kept
named obligation is the reduced native contract supply below, not the full
NativeOldC1Bridge.  The bridge itself remains conditional on
C10BridgeProof.NativeOriginalInputDonors and NativePlaceBindingDonors.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C10DonorSearch

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive}

/-- Reduced exact missing production donor: a contract record over the native
arithmetic root.  This replaces the full NativeOldC1Bridge obligation: the remaining
gap is only the native contract supply, not the entire bridge. -/
def NativeContractSupply (X : N8NativeInput l) : Prop :=
  ∃ initial : SourceDefinition31Data.{0} l,
    initial.arithmetic = X.S.arithmetic

/-- Found donor: native place bijection to the old finite/infinite place index. -/
noncomputable def nativePlaceEquivDonor (X : N8NativeInput l) :
    NativePlaces X.S ≃ NumberFieldPlaceIndex (F := X.S.arithmetic.Fmod) :=
  nativePlaceIndexEquiv X

/-- Found donor: selected native place (bad place). -/
noncomputable def nativeSelectedPlaceDonor (X : N8NativeInput l) : NativePlaces X.S :=
  badPlace X

end LeanFormal.IUT.N8Closure.C10DonorSearch
