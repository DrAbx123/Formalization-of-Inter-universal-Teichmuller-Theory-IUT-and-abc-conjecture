import tmp.sheaf.xif.paper.Mzk1Hull13BothSidedBaseActual
import tmp.sheaf.xif.paper.Mzk1Hull13H7Ob9ComparisonConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# Mzk1H7Ob9BundleStubConsumerActual — HULL.H7.OB9.BUNDLE stub implementation

Implements the DAG stub node iutiii:IUTIII.HULL.H7.OB9.BUNDLE by consuming the
Hull13 base two-sided inputs and the H7/Ob9 comparison consumer: Cor 3.12
hull+det conclusion plus the base upper-bound projection.
No sorry/axioms; conditional on explicit named base-lower-bound input. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1H7Ob9BundleStubConsumerActual

universe ua uv upi umon ui u

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual
open LeanFormal.IUT.XiFPaper.Indet05RouteMultiradialClassActual
open LeanFormal.IUT.XiFPaper.Indet06H7Ob9WiringActual
open LeanFormal.IUT.XiFPaper.Hull10H7Ob9ConsumerActual
open LeanFormal.IUT.XiFPaper.Hull12Ob9BoundTransferActual
open LeanFormal.IUT.XiFPaper.Hull13H7Ob9ComparisonConsumerActual
open LeanFormal.IUT.XiFPaper.Hull13TwoSidedBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1Hull13BothSidedBaseActual
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual

variable {l : PrimeGeFive} {V : Type uv}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- **PROVED (conditional):** Cor 3.12 hull+det conclusion from base two-sided inputs. -/
theorem h7ob9Stub_cor (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9BaseTwoSidedInputs (l := l) M I) :
    Cor312HullDetConclusion M In.twoSided.comparison.consumer.hull.theta :=
  (hull13_baseTwoSided (M := M) I In).1

/-- **PROVED (conditional):** base upper bound projection. -/
theorem h7ob9Stub_upper (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9BaseTwoSidedInputs (l := l) M I) :
    ∀ z, z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.twoSided.comparison.consumer.base) →
      z ≤ In.twoSided.comparison.bound :=
  fun z hz => ((hull13_baseTwoSided (M := M) I In).2.1 z hz).2

/-- **PROVED (conditional):** base lower-bound projection (named transfer input). -/
theorem h7ob9Stub_lower (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9BaseTwoSidedInputs (l := l) M I) :
    ∀ z, z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.twoSided.comparison.consumer.base) →
      In.baseLowerBound ≤ z :=
  fun z hz => ((hull13_baseTwoSided (M := M) I In).2.1 z hz).1

def h7ob9StubRows : List (String × String × String) :=
  [ ("Cor312 hull+det conclusion", "PROVED (conditional)", "h7ob9Stub_cor"),
    ("base upper bound", "PROVED (conditional)", "h7ob9Stub_upper"),
    ("base lower bound (named transfer)", "PROVED (conditional)", "h7ob9Stub_lower") ]

theorem h7ob9StubRows_length : h7ob9StubRows.length = 3 := rfl

#check h7ob9Stub_cor
#check h7ob9StubRows_length

end LeanFormal.IUT.XiFPaper.Mzk1H7Ob9BundleStubConsumerActual
end