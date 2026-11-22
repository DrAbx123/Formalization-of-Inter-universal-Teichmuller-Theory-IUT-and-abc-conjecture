import tmp.sheaf.xif.paper.S3136LGPThetaValueSymmetryActual

/-! # Stage-4 host: theta-value sign symmetry power law

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103); IUT II theta values;
IUT III, Prop. 3.7, (iii), (iv) (pp. 109--111).

This file combines the actual sign symmetry of theta values with the actual
theta/q_v power law: the negated label has the same (2l)-th power readout.

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPThetaValueNegPowActual

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
open LeanFormal.IUT.XiFPaper.S3136LGPThetaValueSymmetryActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The (2l)-th power of the negated theta value is the q_v power at the same
label: theta_{-j}^{2l} = theta_j^{2l} = q_v^{j^2}. -/
theorem lgpThetaValue_neg_pow_twoL (b : Bad (nativePlaceSelection T))
    (j : LGPThetaIndex l) :
    (lgpThetaValue T b (lgpThetaLabelNeg j)) ^ (2 * l.value) =
      qVAlgClosedUnit T b ^ lgpThetaExponent l j := by
  rw [lgpThetaValue_neg]
  exact lgpThetaValue_pow_twoL (l := l) T b j

#check lgpThetaValue_neg_pow_twoL

end LeanFormal.IUT.XiFPaper.S3136LGPThetaValueNegPowActual
end