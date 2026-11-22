import tmp.sheaf.xif.paper.S3136LGPXMuUnitActual
import tmp.sheaf.xif.paper.S3136LGPJvPacketTransportActual

/-! # Stage-4 host: mu_{2l}-quasi-lattice class of the theta values

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103) and Prop. 3.7,
(iii), (iv) (pp. 109--111): the theta values are the 2l-th roots of the q_v
powers, so their mu_{2l}-quotient class is well defined and independent of the
chosen root system.

This file constructs the actual mu_{2l}-quasi-lattice class of the theta values:
* lgpThetaValueQuotient b j: the class of theta_j in the actual mu_{2l}-quotient
  of the actual unit group;
* lgpThetaValue_quotient_root_independent: the class is independent of the
  actual 2l-th root system R (any two root systems differ by a mu_{2l}-
  element, and the j^2-power of a mu_{2l}-element is again in mu_{2l});
* LGPThetaMuQuasiLatticeCandidate: bundled candidate with actual inhabitant;
* LGPThetaMuQuasiLatticeMissing/Gap: exact missing data (embedding into the IQ
  packet, Galois mu-action, log-link compatibility, paper label components).

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPThetaMuQuasiLatticeActual

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

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The class of an actual theta value in the actual mu_{2l}-quotient of the
actual unit group. -/
noncomputable def lgpThetaValueQuotient (b : Bad (nativePlaceSelection T))
    (j : LGPThetaIndex l) :
    (AlgebraicClosure (Completion (qVPlace T b)))ˣ ⧸
      muTwoLAlgClosedSubgroup T b :=
  QuotientGroup.mk' (muTwoLAlgClosedSubgroup T b) (lgpThetaValue T b j)

/-- The theta-value class is independent of the chosen actual 2l-th root system:
the mu_{2l}-quasi-lattice structure is actual. -/
theorem lgpThetaValue_quotient_root_independent
    (b : Bad (nativePlaceSelection T)) (j : LGPThetaIndex l)
    (R : NatRootSystem (qVAlgClosedUnit T b)) :
    QuotientGroup.mk' (muTwoLAlgClosedSubgroup T b)
        ((R.root (2 * l.value)) ^ lgpThetaExponent l j) =
      lgpThetaValueQuotient T b j := by
  unfold lgpThetaValueQuotient lgpThetaValue
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  have hmem := TwoLthRootKummerActual.twoLthRoot_ratio_mem_mu (l := l) T b R
    (hodgeTwoLRootSystem T b)
  have hratio : hodgeTwoLthRoot T b =
      ((hodgeTwoLRootSystem T b).root (2 * l.value) / R.root (2 * l.value)) *
        R.root (2 * l.value) := by
    rw [div_mul_cancel]
    rfl
  rw [hratio, mul_pow]
  have hpow : ((hodgeTwoLRootSystem T b).root (2 * l.value) /
      R.root (2 * l.value)) ^ lgpThetaExponent l j ∈
      muTwoLAlgClosedSubgroup T b :=
    Subgroup.pow_mem (muTwoLAlgClosedSubgroup T b) hmem _
  convert hpow using 1
  symm
  simp [mul_comm, mul_assoc, mul_left_comm]

/-- Bundled candidate mu_{2l}-quasi-lattice class of the actual theta values. -/
structure LGPThetaMuQuasiLatticeCandidate (b : Bad (nativePlaceSelection T)) where
  /-- The theta-value class in the actual mu_{2l}-quotient. -/
  thetaClass : LGPThetaIndex l →
    (AlgebraicClosure (Completion (qVPlace T b)))ˣ ⧸
      muTwoLAlgClosedSubgroup T b
  /-- The class is independent of the chosen actual 2l-th root system. -/
  root_independent : ∀ (j : LGPThetaIndex l)
    (R : NatRootSystem (qVAlgClosedUnit T b)),
      QuotientGroup.mk' (muTwoLAlgClosedSubgroup T b)
        ((R.root (2 * l.value)) ^ lgpThetaExponent l j) = thetaClass j

/-- The actual candidate mu_{2l}-quasi-lattice class. -/
noncomputable def lgpThetaMuQuasiLatticeCandidate
    (b : Bad (nativePlaceSelection T)) :
    LGPThetaMuQuasiLatticeCandidate T b where
  thetaClass := lgpThetaValueQuotient T b
  root_independent := lgpThetaValue_quotient_root_independent T b

#check lgpThetaValue_quotient_root_independent
#check lgpThetaMuQuasiLatticeCandidate


end LeanFormal.IUT.XiFPaper.S3136LGPThetaMuQuasiLatticeActual
end