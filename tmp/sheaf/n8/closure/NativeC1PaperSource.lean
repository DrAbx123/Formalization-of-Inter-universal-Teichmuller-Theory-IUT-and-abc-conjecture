import tmp.sheaf.n8.closure.NativeSourceAssembly
import tmp.sheaf.n8.closure.N8NativeClosure
import tmp.sheaf.n8.closure.NativeBindingRFActual

/-! # Native C1 paper-source packet

This file bundles the explicit source input of the paper C1/C10 route:

* X : N8NativeInput l, the native initial Theta data and lattice;
* S : NativeSourceAssembly X.S, the assembled Definition 3.1 contract data;
* e : X.family.index ≃ SourceTheorem311Index, the native index equivalence;
* R : NativeImageRealizationSourceFields at the assembled input;
* F : NativeFiberSourceFields at the assembled input.

From this packet this file derives, without axioms or sorry:

* P6BridgeDonors X;
* NativeOldC1Bridge X;
* C1ActualData (assemblyInput X S e);
* SourceInputBinding (assemblyInput X S e).

The missing paper fields are explicit fields of the packet, not theorem
conclusions.  No arbitrary V, index, realization or fiber map is invented. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.N8Closure.NativeC1PaperSource

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C1Actual
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.N8Closure.NativeBindingRFActual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive}

/-- Complete native C1 paper-source packet.  Every field is actual source data;
the fields R and F are the exact missing paper realizations/fiber fields. -/
structure NativeC1PaperSource (l : PrimeGeFive) where
  /-- Native initial Theta data plus lattice. -/
  X : N8NativeInput l
  /-- Assembled Definition 3.1 contract data. -/
  S : NativeSourceAssembly X.S
  /-- Native theater-family index equivalence. -/
  e : X.family.index ≃ SourceTheorem311Index
  /-- Exact source image realization fields at the assembled input. -/
  R : NativeImageRealizationSourceFields X
    (assemblyInput X S e)
  /-- Exact source fiber-equivalence fields at the assembled input. -/
  F : NativeFiberSourceFields X
    (assemblyInput X S e) (nativePlaceIndexEquiv X)

namespace NativeC1PaperSource

variable (P : NativeC1PaperSource l)

/-- The assembled OriginalInput carried by the packet. -/
abbrev input : OriginalInput l (NativePlaces P.X.S) :=
  assemblyInput P.X P.S P.e

/-- The native index equivalence carried by the packet. -/
abbrev indexEquiv : P.X.family.index ≃ SourceTheorem311Index :=
  P.e

/-- The exact P6 donor package derived from the packet. -/
noncomputable def donors : P6BridgeDonors P.X :=
  p6BridgeDonorsOfAssembly P.X P.S P.e P.R P.F

/-- The old C1 bridge derived from the donor package. -/
noncomputable def nativeOldC1Bridge : NativeOldC1Bridge P.X :=
  P.donors.toNativeOldC1Bridge

/-- The actual C1 data derived from the packet. -/
noncomputable def c1ActualData : C1ActualData P.input :=
  c1ActualDataOfNativeDonors P.X P.donors.inputDonors P.donors.bindingDonors

/-- The actual SourceInputBinding derived from the packet. -/
noncomputable def sourceInputBinding : SourceInputBinding P.input :=
  sourceInputBindingOfNativeDonors P.X P.donors.inputDonors P.donors.bindingDonors

/-- The bridge input is exactly the assembled input. -/
@[simp] theorem nativeOldC1Bridge_input :
    P.nativeOldC1Bridge.input = P.input := rfl

/-- The bridge binding is exactly the derived SourceInputBinding. -/
@[simp] theorem nativeOldC1Bridge_binding :
    P.nativeOldC1Bridge.binding = P.sourceInputBinding := rfl

/-- The C1 data is exactly the data derived from the donor binding. -/
@[simp] theorem c1ActualData_placeEquiv :
    P.c1ActualData.placeEquiv = P.sourceInputBinding.place.placeEquiv := rfl

/-- The SourceInputBinding is derived from the same packet. -/
@[simp] theorem sourceInputBinding_place :
    P.sourceInputBinding.place.selected = nativeSelectedPlace P.X := rfl

/-- The packet yields all four advertised outputs. -/
theorem packet_outputs :
    Nonempty (P6BridgeDonors P.X) ∧
      Nonempty (NativeOldC1Bridge P.X) ∧
      Nonempty (C1ActualData P.input) ∧
      Nonempty (SourceInputBinding P.input) :=
  ⟨⟨P.donors⟩, ⟨P.nativeOldC1Bridge⟩,
    ⟨P.c1ActualData⟩, ⟨P.sourceInputBinding⟩⟩

/-- Existence of the packet is exactly existence of the complete source input
package.  This is not a theorem about arbitrary X. -/
def NativeC1PaperSourceExists : Prop :=
  Nonempty (NativeC1PaperSource l)

/-- Conditional complete C1 paper source: a packet gives the native old C1
bridge and the SourceInputBinding. -/
theorem nativeOldC1Bridge_nonempty_of_packet (P : NativeC1PaperSource l) :
    Nonempty (NativeOldC1Bridge P.X) :=
  ⟨P.nativeOldC1Bridge⟩

/-- Conditional complete C1 paper source: a packet gives C1ActualData and
SourceInputBinding at the assembled input. -/
theorem sourceInputBinding_nonempty_of_packet (P : NativeC1PaperSource l) :
    Nonempty (SourceInputBinding P.input) :=
  ⟨P.sourceInputBinding⟩

/-! ## Exact remaining source inputs

The packet is not constructed unconditionally.  Its fields are exactly the
native/paper source inputs that the current tree does not produce from X:

1. X : N8NativeInput l;
2. S : NativeSourceAssembly X.S;
3. e : X.family.index ≃ SourceTheorem311Index;
4. R : NativeImageRealizationSourceFields X (assemblyInput X S e);
5. F : NativeFiberSourceFields X (assemblyInput X S e) (nativePlaceIndexEquiv X).

Given those fields, all four outputs are derived without arbitrary data,
axioms or sorry.  No unconditional packet existence is asserted. -/

end NativeC1PaperSource

end LeanFormal.IUT.N8Closure.NativeC1PaperSource

end