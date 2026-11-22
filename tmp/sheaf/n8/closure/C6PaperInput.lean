import tmp.sheaf.n8.closure.C6ConstructedBridge
import tmp.sheaf.n8.closure.SourceAllowedOutputActualAttempt
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

/-!
# C6 paper input (SourceInitialThetaData audit)

The paper-shaped source is SourceInitialThetaData.  Its actual arithmetic is
S.candidate.arithmetic, with paper places S.candidate.V / S.candidate.place.

The current C6 donors are stated in terms of the SourceDefinition31Data shell
(C6ContractSupply, NativeOriginalInputDonors).  Therefore this file records the
exact conversion dependency instead of constructing an arbitrary shell:

  C6PaperContractConversionGap S :=
    exists D : SourceDefinition31Data, D.arithmetic = S.candidate.arithmetic.

Given such a conversion D, the native arithmetic alignment
S.candidate.arithmetic = X.S.arithmetic, an index equivalence, and the explicit
selected R/fiber donors, the file constructs NativeOriginalInputDonors,
NativePlaceBindingDonors, P6BridgeDonors and the old C1 bridge.

The output data C2/C3/C4/T11/C6 remain a precise paper-data gap C6PaperOutputGap;
when supplied they construct SourceAllowedOutput J and its Theta readout.
No selected realization or fiber equivalence is invented.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C6PaperInput

universe ua uv upi umon ui uL

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.C6ConstructedBridge
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.SourceAllowedOutputActualAttempt
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C4Actual
open MeasureTheory

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual paper arithmetic projection. -/
def paperArithmetic (S : SourceInitialThetaData l) :=
  S.candidate.arithmetic

/-- Actual paper place-type projection. -/
def paperV (S : SourceInitialThetaData l) :=
  S.candidate.V

/-- Actual paper place projection. -/
def paperPlace (S : SourceInitialThetaData l) (v : paperV S) :=
  S.candidate.place v

/-- Exact shell-conversion dependency: SourceInitialThetaData -> the
SourceDefinition31Data shell used by the C6 donor interfaces. -/
def C6PaperContractConversionGap (S : SourceInitialThetaData l) : Prop :=
  ∃ D : SourceDefinition31Data.{0} l,
    D.arithmetic = paperArithmetic S

/-- Native arithmetic alignment required for a C6 bridge over X. -/
def C6PaperArithmeticAlignment
    (S : SourceInitialThetaData l) : Prop :=
  paperArithmetic S = X.S.arithmetic

/-- Actual C6 contract supply from an explicit conversion datum and the native
arithmetic alignment. -/
theorem c6ContractSupply_of_paperData
    (S : SourceInitialThetaData l)
    (D : SourceDefinition31Data.{0} l)
    (hD : D.arithmetic = paperArithmetic S)
    (ha : C6PaperArithmeticAlignment X S) :
    C6ContractSupply X :=
  ⟨D, hD.trans ha⟩

/-- Explicit paper index data constructs the C6 index supply. -/
theorem c6IndexSupply_of_paperData
    (e : X.family.index ≃ SourceTheorem311Index) :
    C6IndexSupply X :=
  ⟨e⟩

/-- Actual native original input from the conversion datum and paper index. -/
noncomputable def paperInputOf
    (S : SourceInitialThetaData l)
    (D : SourceDefinition31Data.{0} l)
    (hD : D.arithmetic = paperArithmetic S)
    (ha : C6PaperArithmeticAlignment X S)
    (e : X.family.index ≃ SourceTheorem311Index) :
    NativeOriginalInputDonors X :=
  nativeOriginalInputDonorsOf X (c6ContractSupply_of_paperData X S D hD ha) e

/-- Actual P6 bridge donors from the paper fields and explicit R/fiber data. -/
noncomputable def paperBridgeDonorsOf
    (S : SourceInitialThetaData l)
    (D : SourceDefinition31Data.{0} l)
    (hD : D.arithmetic = paperArithmetic S)
    (ha : C6PaperArithmeticAlignment X S)
    (e : X.family.index ≃ SourceTheorem311Index)
    (R : (nativeOriginalInputOfDonors X (paperInputOf X S D hD ha e)).SourceImageRealization
      (badPlace X))
    (F : ∀ (n m : Int) (v : NativePlaces X.S),
      ((nativeOriginalInputOfDonors X (paperInputOf X S D hD ha e)).primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup
          (F := (paperInputOf X S D hD ha e).initial.arithmetic.Fmod)
          (((paperInputOf X S D hD ha e).initial_arithmetic ▸ nativePlaceIndexEquiv X) v)) :
    P6BridgeDonors X :=
  c6BridgeDonorsOf X
    (c6ContractSupply_of_paperData X S D hD ha) e R F

/-- Actual old C1 bridge derived from the paper bridge donors. -/
noncomputable def paperBridgeOf
    (S : SourceInitialThetaData l)
    (D : SourceDefinition31Data.{0} l)
    (hD : D.arithmetic = paperArithmetic S)
    (ha : C6PaperArithmeticAlignment X S)
    (e : X.family.index ≃ SourceTheorem311Index)
    (R : (nativeOriginalInputOfDonors X (paperInputOf X S D hD ha e)).SourceImageRealization
      (badPlace X))
    (F : ∀ (n m : Int) (v : NativePlaces X.S),
      ((nativeOriginalInputOfDonors X (paperInputOf X S D hD ha e)).primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup
          (F := (paperInputOf X S D hD ha e).initial.arithmetic.Fmod)
          (((paperInputOf X S D hD ha e).initial_arithmetic ▸ nativePlaceIndexEquiv X) v)) :
    NativeOldC1Bridge X :=
  (paperBridgeDonorsOf X S D hD ha e R F).toNativeOldC1Bridge

/-- Precise paper-data gap for C2/C3/C4/T11/C6 output data over a bridge donor. -/
structure C6PaperOutputData (P : P6BridgeDonors X) where
  C2 : SourceLogKummerData (actualBridge P).input (actualBridge P).binding
  C3 : SourcePilotRegionData (actualBridge P).input
  D : SourceWitnessedOutputData (actualBridge P).input (PaperLabel l)
  T : SourceThetaIQInterface (I := (actualBridge P).input) C3
  [measurableSpace : MeasurableSpace
    (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  [borelSpace : BorelSpace
    (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)
  [addHaar : Measure.IsAddHaarMeasure mu]
  B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu

/-- Conditional actual SourceAllowedOutput J from bridge donors and the precise
output data. -/
noncomputable def paperSourceAllowedOutput
    (P : P6BridgeDonors X) (A : C6PaperOutputData X P) :
    SourceAllowedOutput X :=
  sourceAllowedOutputOfActualData
    { donors := P
      C2 := A.C2
      C3 := A.C3
      D := A.D
      T := A.T
      measurableSpace := A.measurableSpace
      borelSpace := A.borelSpace
      mu := A.mu
      addHaar := A.addHaar
      B := A.B }

/-- C6 Theta readout of J. -/
noncomputable def paperTheta (J : SourceAllowedOutput X) : ℝ :=
  J.ellOut

/-- Exact remaining output-data gap. -/
def C6PaperOutputGap (P : P6BridgeDonors X) : Prop :=
  Nonempty (C6PaperOutputData X P)

/-- Conditional actual J existence from the output-data gap. -/
theorem paperSourceAllowedOutput_nonempty_of_gap
    (P : P6BridgeDonors X) (h : C6PaperOutputGap X P) :
    Nonempty (SourceAllowedOutput X) := by
  obtain ⟨A⟩ := h
  exact ⟨paperSourceAllowedOutput X P A⟩

end LeanFormal.IUT.N8Closure.C6PaperInput
