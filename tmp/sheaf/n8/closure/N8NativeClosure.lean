import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.n8.closure.NativeC1
import tmp.sheaf.n8.closure.TargetSignature
import tmp.sheaf.n8.closure.SourceInputBinding

/-!
# N8 native closure: interface slice

This file starts the native C1 assembly from S/lattice and records the exact
C1-C9 dependency/call points for the final native assembly.  It does not modify
N8Closure.lean and does not claim closure.

## C1 (constructed here)

NativeC1Data packages the actual native C1 data:
- placeEquiv : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := Fmod)
- placeEquiv_comap
- selected place (the native bad place) with membership and comap
- local field/value group carriers (native localFieldAt/valueGroupAt)
- completion restriction for finite native places

All fields are built from NativeInput/NativeC1 without new assumptions.

## Exact C1 bridge to old C1-C9

The old C1-C9 chain is indexed by OriginalInput, while the native root is
N8NativeInput (SourceNativeInitialThetaData + NativeLattice).  There is no
native -> SourceDefinition31Data -> OriginalInput constructor in the tree:
SourceDefinition31NativeContractBridgeReduction only states an existential
bridge.  Therefore the old chain cannot be called yet.

NativeOldC1Bridge below is the exact missing interface:
  input : OriginalInput l (NativePlaces X.S)
  binding : SourceInputBinding input

## C1-C9 native dependency / call-point list

C1 (native): NativeC1Data X; actual terms from NativeC1.
C2: SourceLogKummerData oldInput oldC1; needs actual local log/Kummer/root
    completion objects at native finite places.  NativeC1 currently has
    completionRestriction but not the log/Kummer carrier.
C3: SourcePilotRegionData oldInput; needs actual q/theta/tensor data.
C4: SourceWitnessedOutputData oldInput Label; needs C3 pilot and Ind action.
C5: SourceAlgorithmCompatibilityData oldInput oldC1 oldC2 oldC3 oldC4;
    needs permitted family/algorithm compatibility.
C6: PaperNormalizedVolumeData; needs actual native places/tuple/Haar measure
    and lambda/tuple weights (not in NativeInput).
C7: SourceHolomorphicHullData (actual IQ) over C6ActualIQData; needs C3 tensor
    fields and C6 product/measure bridge.
C8: C8IQ.sourceDegreeComparisonIQ over C7.
C9: C9IQ.sourcePilotApproximationIQ_stage2 over C7/C8.

Actual call points are the corresponding declarations in the imported closure
files; the missing prerequisite for all of C2-C9 is the native -> old C1 bridge
and the native C2/C3/C6 data, not another C10-level wrapper.
## Native C1-C9 actual call points (parallel native slices)

These are the concrete native declarations the final assembly must call; this
file only packages C1 and the missing old-chain bridge.

C1: NativeC1Data (this file) and NativeC1.placeEquiv_comap / badPlace_comap.
C2: C2Native.nativeLocalShell, C2Native.NativeLogSlice, C2Native.nativeLogSlice.
C3: NativeC3.nativeQ, nativeQUnit, nativeQUnitAlgClosed, nativeRoots,
    nativeKummerClass, NativeQDonor, NativeTensorLandingDonor,
    NativeC3Data, nativeC3DataOfDonors.
C4: old SourceWitnessedOutputData (no NativeC4 file yet).
C5: C5Native.nativeIPLFamily, fPrimeStripLinkOfEquiv, NativeSHEActual,
    nativeSHEActual, NativeAPTMissing.
C6: C6ActualIQData (no NativeC6 assembly file yet); needs the actual native
    places/tuple/Haar measure.
C7: C7Native.sourcePaperHull, sourceU_subset_sourcePaperHull,
    sourceHolomorphicHullData_nonempty_of_native, SourceUToIQDonor,
    ThetaImageContainmentDonor, QPilotHullMembershipDonor.
T11: T11Native.nativeThetaValue, nativeThetaValue_completion,
    nativeThetaValue_realReadout, ThetaPacketIdentification,
    C4ValueMonoidToIQMissing.
C8: old C8IQ.sourceDegreeComparisonIQ (no NativeC8 file yet).
C9: C9Native.QSigned, ThetaSigned, Values, ActualValuesBounded,
    ActualQApproximated, MissingSourceQHullComparison,
    MissingValuesBoundedByTheta.

The exact old-chain bridge is NativeOldC1Bridge below; it is the first missing
interface for all C2-C9 calls.  No free type, placeholder, unconditional field or empty carrier is used.

-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeClosure

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.N8Closure.TargetSignature
open LeanFormal.IUT.N8Closure.SourceInputBinding

variable {l : PrimeGeFive}

/-- Constructed native C1 data from S/lattice. -/
structure NativeC1Data (X : N8NativeInput l) where
  /-- Native place bijection to the actual base places. -/
  placeEquiv : NativePlaces X.S ≃ NumberFieldPlace X.S.arithmetic.Fmod
  /-- The bijection is the actual comap place equivalence. -/
  placeEquiv_comap : ∀ v : NativePlaces X.S,
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1 = placeEquiv v
  /-- The selected native place (native bad place). -/
  selected : NativePlaces X.S
  /-- The selected place belongs to the native place subtype. -/
  selected_mem : selected.1 ∈ X.S.tuple.source.V
  /-- Its base place is the native bad base place. -/
  selected_comap :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) selected.1 =
      NumberFieldPlace.finite (badBasePlace X)

/-- Actual native C1 data. -/
noncomputable def nativeC1Data (X : N8NativeInput l) : NativeC1Data X where
  placeEquiv := placeEquiv X
  placeEquiv_comap := placeEquiv_comap X
  selected := badPlace X
  selected_mem := (badPlace X).2
  selected_comap := badPlace_comap X

/-- Exact missing bridge from the native C1 root to the old C1-C9 chain. -/
structure NativeOldC1Bridge (X : N8NativeInput l) where
  input : OriginalInput l (NativePlaces X.S)
  binding : SourceInputBinding input

/-- Existence of the native -> old C1 bridge is the first exact missing
interface; no inhabitant is constructed here. -/
def NativeOldC1BridgeExists (X : N8NativeInput l) : Prop :=
  Nonempty (NativeOldC1Bridge X)

/-- C1 native place bijection as a standalone theorem. -/
theorem nativeC1_placeEquiv_comap (X : N8NativeInput l) (v : NativePlaces X.S) :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1 =
      placeEquiv X v :=
  placeEquiv_comap X v

/-- C1 native selected place is the bad place. -/
theorem nativeC1_selected_comap (X : N8NativeInput l) :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) (badPlace X).1 =
      NumberFieldPlace.finite (badBasePlace X) :=
  badPlace_comap X

end LeanFormal.IUT.N8Closure.NativeClosure
