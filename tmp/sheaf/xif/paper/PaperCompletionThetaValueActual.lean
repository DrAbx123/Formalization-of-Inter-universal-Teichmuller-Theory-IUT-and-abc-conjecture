/-
INVALID AS PAPER OBJECT (completion 2l-th root audit).

This file depends on a completion 2l-th root q_v^(1/2l) of the qVFamily q
(PaperQRootCard / NatRootSystem (qVUnit ...) / HalfRootInCompletion).
S342QVFamilyRootImpossibleActual proves that this is impossible: the order is
coprime to l while a 2l-th root forces 2l | order.  The conditional records
and consequences below are retained only as invalidated history; they must not
be used as paper objects or as inputs to further constructions.
-/
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction
import tmp.sheaf.n8.closure.NativeBadLiftActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual

noncomputable section
open scoped BigOperators Pointwise
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual

namespace LeanFormal.IUT.XiFPaper.PaperCompletionThetaValueActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))

/-- The paper q_v^(1/2l) card at the actual qVFamily parameter, in the completion. -/
abbrev PaperQRootCard : Type :=
  QParameterTwoLRootCard l ((nativeBadLift T).lift b) (qVFamily T b)

/-- The completion root underlying the paper theta value. -/
noncomputable def paperQRoot (R : PaperQRootCard T b) :
    Completion ((nativeBadLift T).lift b) := R.root

theorem paperQRoot_pow (R : PaperQRootCard T b) :
    paperQRoot T b R ^ (2 * l.value) = (qVFamily T b).q := by
  unfold paperQRoot
  exact R.root_pow

theorem paperQRoot_ne_zero (R : PaperQRootCard T b) :
    paperQRoot T b R ≠ 0 := by
  unfold paperQRoot
  exact R.root_ne_zero

/-- Paper theta value q[2u]_v^(j^2) = (q_v^(1/2l))^(j^2), in the completion. -/
noncomputable def paperCompletionThetaValue
    (R : PaperQRootCard T b) (j : ThetaLabel (l := l)) :
    Completion ((nativeBadLift T).lift b) :=
  paperQRoot T b R ^ (gaussExponent (thetaLabelToSigned (l := l) j).1).toNat

theorem paperCompletionThetaValue_pow_twoL
    (R : PaperQRootCard T b) (j : ThetaLabel (l := l)) :
    paperCompletionThetaValue T b R j ^ (2 * l.value) =
      (qVFamily T b).q ^
        (gaussExponent (thetaLabelToSigned (l := l) j).1).toNat := by
  unfold paperCompletionThetaValue
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  rw [paperQRoot_pow]

theorem paperCompletionThetaValue_ne_zero
    (R : PaperQRootCard T b) (j : ThetaLabel (l := l)) :
    paperCompletionThetaValue T b R j ≠ 0 := by
  unfold paperCompletionThetaValue
  exact pow_ne_zero _ (paperQRoot_ne_zero T b R)

/-- Completion theta image set over the positive paper labels. -/
noncomputable def paperCompletionThetaImageSet
    (R : PaperQRootCard T b) : Set (Completion ((nativeBadLift T).lift b)) :=
  Set.range (paperCompletionThetaValue T b R)

theorem paperCompletionThetaValue_mem_image
    (R : PaperQRootCard T b) (j : ThetaLabel (l := l)) :
    paperCompletionThetaValue T b R j ∈ paperCompletionThetaImageSet T b R :=
  ⟨j, rfl⟩

/-- The root card is the exact source input; this records it without claiming an inhabitant. -/
def PaperQRootCardGap : Prop := Nonempty (PaperQRootCard T b)

end LeanFormal.IUT.XiFPaper.PaperCompletionThetaValueActual
end