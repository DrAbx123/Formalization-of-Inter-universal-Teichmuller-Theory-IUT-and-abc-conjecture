import tmp.sheaf.xif.paper.S3136LGPThetaMuQuasiLatticeActual
import tmp.sheaf.xif.paper.S3136LGPThetaValueSymmetryActual

/-! # Stage-4 host: mu_{2l}-quasi-lattice class of the negated label

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103).

The actual sign symmetry of theta values implies that the mu_{2l}-quasi-lattice
class of the negated label equals the class of the label: the plus/minus pairing is
already trivial at the level of the actual quasi-lattice classes.

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPThetaQuotientNegActual

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
open LeanFormal.IUT.XiFPaper.S3136LGPThetaValueSymmetryActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The mu_{2l}-quasi-lattice class is invariant under label negation. -/
theorem lgpThetaValueQuotient_neg (b : Bad (nativePlaceSelection T))
    (j : LGPThetaIndex l) :
    lgpThetaValueQuotient T b (lgpThetaLabelNeg j) =
      lgpThetaValueQuotient T b j := by
  unfold lgpThetaValueQuotient
  rw [lgpThetaValue_neg]

#check lgpThetaValueQuotient_neg

end LeanFormal.IUT.XiFPaper.S3136LGPThetaQuotientNegActual
end