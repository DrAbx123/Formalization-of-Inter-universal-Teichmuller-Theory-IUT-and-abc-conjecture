import tmp.sheaf.xif.paper.S3136LGPJvPacketTransportActual

/-! # Stage-4 host: theta-value sign symmetry (label-j pairing)

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103): the label-j components
of the local LGP-monoid act on IQ(S^pm_{j+1,j}; Fv); IUT II theta values.

This file records the actual sign symmetry of the LGP theta values, which is the
algebraic content of the plus/minus label pairing in the tensor packets:
* lgpThetaLabelNeg j: the negated signed theta label (still in SignedLabel);
* lgpThetaValue_neg: theta_{-j} = theta_j (the theta value depends only on j^2);
* LGPThetaLabelSymmetryMissing/Gap: exact missing data for the packet-level
  plus/minus pairing (IQ component pairing, Galois pairing, log-link pairing).

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPThetaValueSymmetryActual

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

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The negated signed theta label. -/
def lgpThetaLabelNeg (j : LGPThetaIndex l) : LGPThetaIndex l :=
  ⟨-j.1, by
    obtain ⟨h1, h2⟩ := j.2
    constructor <;> omega⟩

/-- The actual theta value depends only on the square of the label: the negated
label has the same theta value (the plus/minus label symmetry). -/
theorem lgpThetaValue_neg (b : Bad (nativePlaceSelection T))
    (j : LGPThetaIndex l) :
    lgpThetaValue T b (lgpThetaLabelNeg j) = lgpThetaValue T b j := by
  unfold lgpThetaValue lgpThetaExponent lgpThetaLabelNeg
  simp

/-- Exact missing data for the packet-level plus/minus label pairing (IUT III,
Prop. 3.4, (ii), pp. 102--103): IQ component pairing, Galois pairing, log-link
pairing, and the mu_{2l}-quasi-lattice pairing. -/
structure LGPThetaLabelSymmetryMissing where
  iqComponentPairing : Prop
  galoisPairing : Prop
  logLinkPairing : Prop
  muQuasiLatticePairing : Prop

/-- The exact plus/minus label pairing gap. -/
def LGPThetaLabelSymmetryGap : Prop :=
  Nonempty LGPThetaLabelSymmetryMissing

#check lgpThetaLabelNeg
#check lgpThetaValue_neg
#check LGPThetaLabelSymmetryGap

end LeanFormal.IUT.XiFPaper.S3136LGPThetaValueSymmetryActual
end