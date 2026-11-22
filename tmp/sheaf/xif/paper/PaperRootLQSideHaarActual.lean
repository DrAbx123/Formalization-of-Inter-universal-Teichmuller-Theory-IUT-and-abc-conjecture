import tmp.sheaf.xif.paper.PaperRootLThetaMigratedActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual

-- S298: qside Haar/hull objects imported and connected on theta labels;
-- the full RootLValuedCarrier ↔ rootTensorBlock linear equivalence remains an
-- exact carrier gap (no fake map).

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.PaperRootLQSideHaarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootLThetaMigratedActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped TensorProduct

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Actual qside theta image/hull/Haar objects.
noncomputable def qSideThetaImage : Set (rootTensorBlock T b) := blockThetaImageSetTheta T b
noncomputable def qSideThetaScaledHull : Set (rootTensorBlock T b) := blockThetaScaledHull T b
noncomputable def qSideSingleScaledRegion : Set (rootTensorBlock T b) := singleScaledRegion T b
noncomputable def qSideHaar : Measure (rootTensorBlock T b) := blockHaar T b
noncomputable def qSideSingleScaledMeasure : ENNReal := singleScaledRegionMeasure T b
noncomputable def qSideSingleScaledLog : Real := singleScaledRegionLog T b

-- Exact missing full carrier equivalence.
structure RootLCarrierToRootTensorEquivGap where
  toRootTensor : Carrier T b → rootTensorBlock T b
  toCarrier : rootTensorBlock T b → Carrier T b
  left_inv : Function.LeftInverse toCarrier toRootTensor
  right_inv : Function.RightInverse toCarrier toRootTensor
  theta_compat : Prop

def RootLCarrierToRootTensorEquivGapRequired : Prop :=
  Nonempty (RootLCarrierToRootTensorEquivGap T b)

#check qSideThetaImage
#check qSideThetaScaledHull
#check qSideSingleScaledRegion
#check qSideHaar
#check qSideSingleScaledMeasure
#check qSideSingleScaledLog
#check RootLCarrierToRootTensorEquivGap

end LeanFormal.IUT.XiFPaper.PaperRootLQSideHaarActual

end