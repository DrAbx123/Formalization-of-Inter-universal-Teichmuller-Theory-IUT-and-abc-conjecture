import tmp.sheaf.xif.paper.S3136LGPThetaMuQuasiLatticeActual

/-! # Stage-4 host: mu_{2l}-quasi-lattice classes and the q_v root direction

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103); IUT III, Prop. 3.7,
(iii), (iv) (pp. 109--111).

This file relates the actual mu_{2l}-quasi-lattice class of the theta values to
the actual q_v 2l-th root direction:
* lgpThetaValueQuotient_pow_twoL: the (2l)-th power of the theta class is the
  class of q_v^{j^2};
* lgpRootQuotient_pow_twoL: the (2l)-th power of the root class is the class of
  the actual q_v unit (the principal q_v compatibility at the quotient level).

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPThetaQuotientQvActual

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

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The (2l)-th power of the theta class is the class of q_v^{j^2}. -/
theorem lgpThetaValueQuotient_pow_twoL (b : Bad (nativePlaceSelection T))
    (j : LGPThetaIndex l) :
    (lgpThetaValueQuotient T b j) ^ (2 * l.value) =
      QuotientGroup.mk' (muTwoLAlgClosedSubgroup T b)
        (qVAlgClosedUnit T b ^ lgpThetaExponent l j) := by
  unfold lgpThetaValueQuotient
  rw [← map_pow, lgpThetaValue_pow_twoL]

/-- The (2l)-th power of the root class is the class of the actual q_v unit
(principal q_v compatibility at the mu_{2l}-quotient level). -/
theorem lgpRootQuotient_pow_twoL (b : Bad (nativePlaceSelection T)) :
    (QuotientGroup.mk' (muTwoLAlgClosedSubgroup T b) (hodgeTwoLthRoot T b)) ^
        (2 * l.value) =
      QuotientGroup.mk' (muTwoLAlgClosedSubgroup T b) (qVAlgClosedUnit T b) := by
  rw [← map_pow, hodgeTwoLthRoot_pow]

#check lgpThetaValueQuotient_pow_twoL
#check lgpRootQuotient_pow_twoL

end LeanFormal.IUT.XiFPaper.S3136LGPThetaQuotientQvActual
end