import tmp.sheaf.xif.paper.S342QVFamilyRootImpossibleActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual

-- S424 audit: repo qVFamily is the F-side clause-B q-parameter with order
-- coprime to l; paper Example 3.2(iv) q_v is the K_v-side base change.
-- The K_v root data is recorded as exact missing, not fabricated.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S424QVFamilyPaperQAuditActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Repo qVFamily lives in the completion of the actual F-place over b.
theorem qVFamily_repo_place_base :
    qVFamilyPlace T b = (nativeBadLift T).lift b := rfl

-- The repo order is coprime to l, exactly paper Definition 3.1(c).
theorem qVFamily_repo_order_coprime :
    Nat.Coprime (qVFamily T b).order l.value :=
  qVFamily_order_coprime T b

-- Any completion 2l-root of the repo qVFamily is impossible (S342).
theorem qVFamily_repo_completion_root_impossible :
    ¬ Nonempty (TwoLthRootData T b) :=
  twoLthRootData_impossible T b

-- Exact missing K_v-side paper data: q_v after base change to K_v, its
-- 2l-th root, and the O^tri root-stack section.
structure PaperKvQRootData where
  Kv : Type
  [fieldKv : Field Kv]
  [algebraKv : Algebra T.arithmetic.F Kv]
  Kv_eq_paperK : Kv = T.arithmetic.K
  qv : Kv
  qv_is_baseChange : Prop
  root : Kv
  root_pow : root ^ (2 * l.value) = qv
  rootStackSection : Prop

def PaperKvQRootDataRequired : Prop :=
  Nonempty (PaperKvQRootData T b)

-- Typed alignment record: repo F-base and paper K-base are not identified.
structure QVFamilyPaperQAlignment where
  repoBase : Type
  repoBase_eq_F : repoBase = T.arithmetic.F
  paperBase : Type
  paperBase_eq_K : paperBase = T.arithmetic.K
  baseChangeMap : Prop
  paperKvData : PaperKvQRootData T b

def QVFamilyPaperQAlignmentRequired : Prop :=
  Nonempty (QVFamilyPaperQAlignment T b)

#check qVFamily_repo_place_base
#check qVFamily_repo_order_coprime
#check qVFamily_repo_completion_root_impossible
#check PaperKvQRootData
#check QVFamilyPaperQAlignment

end LeanFormal.IUT.XiFPaper.S424QVFamilyPaperQAuditActualAdapted

end