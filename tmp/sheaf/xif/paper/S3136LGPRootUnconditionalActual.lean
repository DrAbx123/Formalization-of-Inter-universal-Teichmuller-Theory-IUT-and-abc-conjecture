import tmp.sheaf.xif.paper.S3136LGPToolReuseRootActual
import tmp.sheaf.xif.paper.LGPThetaActionActual
import tmp.sheaf.xif.paper.S3136LGPJvPacketTransportActual

/-! # Stage-4 host: unconditional theta values from the existing alg-closure root tool

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103); IUT II theta values;
IUT III, Prop. 3.7, (iii), (iv) (pp. 109--111).

The earlier theta-value files use the actual root `hodgeTwoLthRoot` of the
completion root system.  Here the *unconditional* alg-closure root of
`S3136LGPToolReuseRootActual` is consumed instead, giving parallel definitions
with no NatRootSystem hypothesis:
* lgpThetaValueUncond b j = (lgpAlgClosedTwoLthRoot b)^(j^2);
* lgpThetaValueUncond_pow_twoL: (2l)-th power = qV^(j^2);
* lgpThetaValueUncond_signedOne: label-1 value = the alg-closure root;
* the unconditional theta-value subgroup and its actual elements.

LABEL: prerequisite component only.  Consumers: lattice, stepxi C2. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPRootUnconditionalActual

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
open LeanFormal.IUT.XiFPaper.S3136LGPToolReuseRootActual
open LeanFormal.IUT.XiFPaper.S3136LGPJvPacketTransportActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The unconditional theta value from the actual alg-closure 2l-th root. -/
noncomputable def lgpThetaValueUncond (b : Bad (nativePlaceSelection T))
    (j : LGPThetaIndex l) : (AlgebraicClosure (Completion (qVPlace T b)))ˣ :=
  (lgpAlgClosedTwoLthRoot T b) ^ lgpThetaExponent l j

/-- Its (2l)-th power is the corresponding q_v power. -/
theorem lgpThetaValueUncond_pow_twoL (b : Bad (nativePlaceSelection T))
    (j : LGPThetaIndex l) :
    (lgpThetaValueUncond T b j) ^ (2 * l.value) =
      qVAlgClosedUnit T b ^ lgpThetaExponent l j := by
  unfold lgpThetaValueUncond
  calc
    ((lgpAlgClosedTwoLthRoot T b) ^ lgpThetaExponent l j) ^ (2 * l.value)
        = (lgpAlgClosedTwoLthRoot T b) ^
            (lgpThetaExponent l j * (2 * l.value)) := by rw [← pow_mul]
    _ = (lgpAlgClosedTwoLthRoot T b) ^
            ((2 * l.value) * lgpThetaExponent l j) := by rw [Nat.mul_comm]
    _ = ((lgpAlgClosedTwoLthRoot T b) ^ (2 * l.value)) ^
            lgpThetaExponent l j := by rw [← pow_mul]
    _ = qVAlgClosedUnit T b ^ lgpThetaExponent l j := by
          rw [lgpAlgClosedTwoLthRoot_pow]

/-- The label-1 unconditional theta value is the alg-closure root. -/
theorem lgpThetaValueUncond_signedOne (b : Bad (nativePlaceSelection T)) :
    lgpThetaValueUncond T b (lgpSignedLabelOne l) = lgpAlgClosedTwoLthRoot T b := by
  unfold lgpThetaValueUncond
  rw [lgpThetaExponent_signedLabelOne, pow_one]

/-- The unconditional theta-value subgroup. -/
def lgpThetaValueUncondSubgroup (b : Bad (nativePlaceSelection T)) :
    Subgroup (AlgebraicClosure (Completion (qVPlace T b)))ˣ :=
  Subgroup.closure (Set.range (lgpThetaValueUncond T b))

/-- The alg-closure 2l-th root lies in the unconditional theta-value subgroup. -/
theorem lgpAlgClosedTwoLthRoot_mem_uncondSubgroup
    (b : Bad (nativePlaceSelection T)) :
    lgpAlgClosedTwoLthRoot T b ∈ lgpThetaValueUncondSubgroup T b := by
  rw [← lgpThetaValueUncond_signedOne T b]
  exact Subgroup.subset_closure ⟨lgpSignedLabelOne l, rfl⟩

/-- The actual q_v unit lies in the unconditional theta-value subgroup. -/
theorem qVAlgClosedUnit_mem_uncondSubgroup (b : Bad (nativePlaceSelection T)) :
    qVAlgClosedUnit T b ∈ lgpThetaValueUncondSubgroup T b := by
  rw [← lgpAlgClosedTwoLthRoot_pow T b]
  exact Subgroup.pow_mem (lgpThetaValueUncondSubgroup T b)
    (lgpAlgClosedTwoLthRoot_mem_uncondSubgroup T b) (2 * l.value)

#check lgpThetaValueUncond
#check lgpThetaValueUncond_pow_twoL
#check lgpThetaValueUncond_signedOne
#check lgpAlgClosedTwoLthRoot_mem_uncondSubgroup
#check qVAlgClosedUnit_mem_uncondSubgroup

end LeanFormal.IUT.XiFPaper.S3136LGPRootUnconditionalActual
end