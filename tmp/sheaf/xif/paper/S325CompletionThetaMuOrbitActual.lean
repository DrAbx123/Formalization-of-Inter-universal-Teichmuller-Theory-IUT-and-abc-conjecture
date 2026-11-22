/-
INVALID AS PAPER OBJECT (completion 2l-th root audit).

This file depends on a completion 2l-th root q_v^(1/2l) of the qVFamily q
(PaperQRootCard / NatRootSystem (qVUnit ...) / HalfRootInCompletion).
S342QVFamilyRootImpossibleActual proves that this is impossible: the order is
coprime to l while a 2l-th root forces 2l | order.  The conditional records
and consequences below are retained only as invalidated history; they must not
be used as paper objects or as inputs to further constructions.
-/
import tmp.sheaf.xif.paper.PaperCompletionThetaValueActual
import Mathlib.RingTheory.RootsOfUnity.Basic
/-! # S325: mu_{2l} orbit of the completion paper theta value
Conditional on R : PaperQRootCard (a 2l-th root of qVFamily q in the completion),
form the actual completion theta value, multiply by zeta in rootsOfUnity(2l),
and construct the mu-orbit and completion theta image union.  No root is faked. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S325CompletionThetaMuOrbitActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperCompletionThetaValueActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (R : PaperQRootCard T b)
abbrev CompletionPlace : Type := Completion ((nativeBadLift T).lift b)
/-- Actual mu_{2l} multiplier in the completion. -/
noncomputable def muCompletionFactor
    (zeta : rootsOfUnity (2 * l.value) (CompletionPlace T b)) :
    CompletionPlace T b :=
  ((zeta : (CompletionPlace T b)ˣ) : CompletionPlace T b)
/-- Actor by a completion 2l-th root of unity. -/
noncomputable def muCompletionAction
    (zeta : rootsOfUnity (2 * l.value) (CompletionPlace T b))
    (x : CompletionPlace T b) : CompletionPlace T b :=
  muCompletionFactor T b zeta * x
/-- Actual zeta-multiplied completion theta value. -/
noncomputable def paperCompletionThetaMuValue
    (zeta : rootsOfUnity (2 * l.value) (CompletionPlace T b))
    (j : ThetaLabel (l := l)) : CompletionPlace T b :=
  muCompletionAction T b zeta (paperCompletionThetaValue T b R j)
/-- The 2l-th power of the zeta-multiplied theta value is the theta power. -/
theorem paperCompletionThetaMuValue_pow_twoL
    (zeta : rootsOfUnity (2 * l.value) (CompletionPlace T b))
    (j : ThetaLabel (l := l)) :
    paperCompletionThetaMuValue T b R zeta j ^ (2 * l.value) =
      paperCompletionThetaValue T b R j ^ (2 * l.value) := by
  unfold paperCompletionThetaMuValue muCompletionAction muCompletionFactor
  rw [mul_pow]
  have hzeta : (((zeta : (CompletionPlace T b)ˣ) : CompletionPlace T b) ^
      (2 * l.value)) = 1 := by
    rw [← Units.val_pow_eq_pow_val]
    have h := zeta.property
    simpa using congrArg
      (fun z : (CompletionPlace T b)ˣ => (z : CompletionPlace T b)) h
  rw [hzeta, one_mul]
/-- mu-action composition law. -/
theorem muCompletionAction_muCompletionAction
    (zeta eta : rootsOfUnity (2 * l.value) (CompletionPlace T b))
    (x : CompletionPlace T b) :
    muCompletionAction T b zeta (muCompletionAction T b eta x) =
      muCompletionAction T b (zeta * eta) x := by
  unfold muCompletionAction muCompletionFactor
  push_cast
  ring
/-- Actual mu_{2l} orbit of the completion theta value at label j. -/
noncomputable def paperCompletionThetaMuOrbit
    (j : ThetaLabel (l := l)) : Set (CompletionPlace T b) :=
  Set.range (fun zeta : rootsOfUnity (2 * l.value) (CompletionPlace T b) =>
    paperCompletionThetaMuValue T b R zeta j)
/-- The completion theta image union over labels and mu-orbit. -/
noncomputable def paperCompletionThetaMuImageUnion :
    Set (CompletionPlace T b) :=
  ⋃ j : ThetaLabel (l := l), paperCompletionThetaMuOrbit T b R j
/-- The plain paper theta value lies in the mu-image union via zeta = 1. -/
theorem paperCompletionThetaValue_mem_muImageUnion
    (j : ThetaLabel (l := l)) :
    paperCompletionThetaValue T b R j ∈ paperCompletionThetaMuImageUnion T b R :=
  Set.mem_iUnion.mpr ⟨j, ⟨1, by
    unfold paperCompletionThetaMuValue muCompletionAction muCompletionFactor
    simp⟩⟩
end LeanFormal.IUT.XiFPaper.S325CompletionThetaMuOrbitActual
