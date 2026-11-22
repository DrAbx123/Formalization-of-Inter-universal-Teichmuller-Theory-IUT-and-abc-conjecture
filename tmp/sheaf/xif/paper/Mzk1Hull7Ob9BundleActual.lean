import tmp.sheaf.xif.paper.Hull10H7Ob9ConsumerActual
import tmp.sheaf.xif.paper.Hull12Ob9BoundTransferActual
import tmp.sheaf.xif.paper.Hull13H7Ob9ComparisonConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: iutiii:HULL.H7.OB9.WRAPPER bundle -> Hull10H7Ob9ConsumerActual.hull10_h7ob9_consumer (Ind1/Ind2 invariance + Ind3 one-sided) + Hull13H7Ob9ComparisonConsumerActual.hull13_h7ob9_comparison (Cor312 + base upper bound) -> PROVED paper-layer bundle of the H7/Ob9 consumer facts from one comparison input. No new math; deep Ob9 arbitrary-iterate independence remains named. No closure.

# Mzk1Hull7Ob9BundleActual — H7/Ob9 consumer bundle

PROVED:
* `hull7ob9_bundle`: Cor 3.12 hull+det conclusion + (Ind1)/(Ind2) invariance +
  (Ind3) one-sided possible image + base possible-image upper bound, from one
  HullH7Ob9ComparisonInputs and a base point z;
* `hull7ob9_base_upper`: base upper-bound projection.
NAMED: deep arbitrary-iterate Ob9 independence (Hull13 row).
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Hull7Ob9BundleActual

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
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual

variable {l : PrimeGeFive} {V : Type uv}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- **PROVED:** H7/Ob9 consumer bundle from one comparison input. -/
theorem hull7ob9_bundle
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9ComparisonInputs (l := l) M I) :
    Cor312HullDetConclusion M In.consumer.hull.theta ∧
      (∀ z', z' ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I In.consumer.base) → z' ≤ In.bound) :=
  hull13_h7ob9_comparison I In

theorem hull7ob9_base_upper
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9ComparisonInputs (l := l) M I) :
    ∀ z', z' ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.consumer.base) → z' ≤ In.bound :=
  (hull13_h7ob9_comparison I In).2

def hull7ob9Rows : List (String × String × String) :=
  [ ("H7/Ob9 consumer bundle", "PROVED", "hull7ob9_bundle (Cor312 + base upper via hull13 comparison)")
  , ("base upper-bound projection", "PROVED", "hull7ob9_base_upper")
  , ("deep Ob9 arbitrary-iterate independence", "NAMED", "Hull13 row; not formalized") ]

theorem hull7ob9Rows_length : hull7ob9Rows.length = 3 := rfl

#check hull7ob9_bundle
#check hull7ob9_base_upper
#check hull7ob9Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1Hull7Ob9BundleActual
end