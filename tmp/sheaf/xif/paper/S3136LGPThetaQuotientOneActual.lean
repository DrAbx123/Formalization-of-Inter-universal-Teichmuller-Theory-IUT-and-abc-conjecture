import tmp.sheaf.xif.paper.S3136LGPThetaQuotientQvActual

/-! # Stage-4 host: the mu_{2l}-class of the label-1 theta value

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103); Prop. 3.7, (iii),
(iv) (pp. 109--111).

The label-1 theta value is the actual 2l-th root, so its mu_{2l}-quasi-lattice
class is the root class, and its (2l)-th power is the class of the actual q_v
unit.

LABEL: prerequisite component only.  Consumer: lattice stream. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPThetaQuotientOneActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.LGPThetaActionActual
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalMonoidActual
open LeanFormal.IUT.XiFPaper.S3136LGPXMuUnitActual
open LeanFormal.IUT.XiFPaper.S3136LGPThetaMuQuasiLatticeActual
open LeanFormal.IUT.XiFPaper.S3136LGPThetaQuotientQvActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The label-1 theta class is the root class. -/
theorem lgpThetaValueQuotient_signedOne (b : Bad (nativePlaceSelection T)) :
    lgpThetaValueQuotient T b (lgpSignedLabelOne l) =
      QuotientGroup.mk' (muTwoLAlgClosedSubgroup T b) (hodgeTwoLthRoot T b) := by
  unfold lgpThetaValueQuotient
  rw [lgpThetaValue_signed_one]

/-- The (2l)-th power of the label-1 class is the class of the actual q_v unit. -/
theorem lgpThetaValueQuotient_signedOne_pow_twoL
    (b : Bad (nativePlaceSelection T)) :
    (lgpThetaValueQuotient T b (lgpSignedLabelOne l)) ^ (2 * l.value) =
      QuotientGroup.mk' (muTwoLAlgClosedSubgroup T b) (qVAlgClosedUnit T b) := by
  rw [lgpThetaValueQuotient_signedOne, lgpRootQuotient_pow_twoL]

#check lgpThetaValueQuotient_signedOne
#check lgpThetaValueQuotient_signedOne_pow_twoL

end LeanFormal.IUT.XiFPaper.S3136LGPThetaQuotientOneActual
end