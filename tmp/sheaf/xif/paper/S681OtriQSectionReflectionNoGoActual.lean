import tmp.sheaf.xif.paper.S677OtriFromTauGapActual
import tmp.sheaf.xif.paper.S342QVFamilyRootImpossibleActual
import tmp.sheaf.xif.paper.TwoLthRootQVActual

-- S681: qSection_reflects_qVFamily cannot be realized in the completion.
-- A completion-valued monoid map sending qSection to qVUnit and respecting
-- root_pow would create a completion 2l-th root, contradicting S342.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S681OtriQSectionReflectionNoGoActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S677OtriFromTauGapActual
open LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open Iut

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (S : Iut.SplitFrobenioidPresentation.{u})
variable (C : OtriCandidateFromTauData (l := l) S)

/-- A completion-valued monoid map on O^triangle units. -/
theorem completionMap_root_pow
    (φ : Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism C.baseObject) →*
      (Completion ((nativeBadLift T).lift b))ˣ)
    (hq : φ (C.qSection : Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism C.baseObject)) =
      qVUnit T b) :
    (φ (C.rootSection : Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism C.baseObject))) ^
        twoLExponent l = qVUnit T b := by
  have hroot :
      ((C.rootSection : C.Otri) :
          Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism C.baseObject)) ^
          twoLExponent l =
        ((C.qSection : C.Otri) :
          Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism C.baseObject)) :=
    congrArg (fun x : C.Otri =>
      (x : Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism C.baseObject)))
      C.root_pow
  rw [← map_pow, hroot, hq]

theorem no_completion_reflection_with_root
    (φ : Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism C.baseObject) →*
      (Completion ((nativeBadLift T).lift b))ˣ)
    (hq : φ (C.qSection : Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism C.baseObject)) =
      qVUnit T b) : False := by
  apply twoLthRootData_impossible (l := l) T b
  refine ⟨?_⟩
  exact
    { root := φ (C.rootSection :
          Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism C.baseObject))
      root_pow := completionMap_root_pow (T := T) (b := b) (S := S) (C := C) φ hq }

/-- Exact reflection data (for the record): a completion map and q-section
image.  No inhabitant due to S342. -/
structure QSectionCompletionReflectionData where
  completionMap : Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism C.baseObject) →*
    (Completion ((nativeBadLift T).lift b))ˣ
  qSection_image :
    completionMap (C.qSection :
      Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism C.baseObject)) = qVUnit T b

def QSectionCompletionReflectionRequired : Prop :=
  Nonempty (QSectionCompletionReflectionData (T := T) (b := b) (S := S) (C := C))

#check no_completion_reflection_with_root
#check QSectionCompletionReflectionData

end LeanFormal.IUT.XiFPaper.S681OtriQSectionReflectionNoGoActual

end