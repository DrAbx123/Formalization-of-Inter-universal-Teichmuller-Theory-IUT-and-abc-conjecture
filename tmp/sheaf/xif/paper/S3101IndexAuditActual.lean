import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.S2717Cor312FullTargetActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3101IndexAuditActual

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0,0,0,0,0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual C3 tensor index. -/
abbrev S3101TensorIndex : Type := C3.tensorIndex

/-- The actual C3 base finite place at tensor index i. -/
noncomputable def S3101C3BasePlace (i : S3101TensorIndex C3) :
    FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p :=
  C3.tensorPlaces i (C3.tensorTuple i)

/-- The actual native bad base finite place at b. -/
noncomputable def S3101NativeBadBasePlace
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.Fmod :=
  b.1

/-- The actual tensor block is exactly the arithmetic tuple block over the
C3 tensor places and tuple. -/
theorem S3101_block_eq :
    C3LogShellTensorBlock C3 =
      ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple := rfl

/-- The actual C3 tensor region lives in the block over C3.tensorPlaces/tuple. -/
theorem S3101_region_def :
    actualC3LogShellTensorRegion C3 =
      tensorIntegralRegion (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
        (fun i => actualC3LogShell C3 i) := rfl

/-- First unproved index equality: the C3 tensor index cardinality equals the
native bad-place cardinality. -/
def S3101IndexCardEquality
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  Fintype.card C3.tensorIndex = Fintype.card (Bad (nativePlaceSelection T))

/-- First unproved base-field equality: the C3 and native bad base fields are
not identified by the concrete C3 donor. -/
def S3101BaseFieldEquality
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  Nonempty (I.initial.arithmetic.Fmod ≃+* T.arithmetic.Fmod)

#check S3101TensorIndex
#check S3101C3BasePlace
#check S3101NativeBadBasePlace
#check S3101_block_eq
#check S3101_region_def
#check S3101IndexCardEquality
#check S3101BaseFieldEquality
#print axioms S3101_block_eq
#print axioms S3101_region_def

end LeanFormal.IUT.XiFPaper.S3101IndexAuditActual
end