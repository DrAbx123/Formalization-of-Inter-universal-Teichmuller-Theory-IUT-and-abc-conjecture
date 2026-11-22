import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

-- S459 candidate only: controlled completion-extension root and Kroot=
-- adjoin(K, root); no paper O^tri claim; order/ramification control exact gap.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S459KrootCandidateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev Kq : Type := Completion (qVFamilyKLift T b)
abbrev ACq : Type := AlgebraicClosure (Kq T b)

def n2l : Nat := 2 * l.value

theorem n2l_pos : 0 < n2l (l := l) := by
  unfold n2l
  exact Nat.mul_pos (by norm_num) l.prime.pos

noncomputable def candidateKRoot : ACq T b :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (Kq T b) (ACq T b) ((qVFamilyK T b).q)) (n2l_pos (l := l)))

theorem candidateKRoot_pow :
    candidateKRoot T b ^ n2l (l := l) =
      algebraMap (Kq T b) (ACq T b) ((qVFamilyK T b).q) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (Kq T b) (ACq T b) ((qVFamilyK T b).q)) (n2l_pos (l := l)))

noncomputable def KrootField : IntermediateField (Kq T b) (ACq T b) :=
  IntermediateField.adjoin (Kq T b) ({candidateKRoot T b} : Set (ACq T b))

abbrev Kroot : Type := KrootField T b

instance krootField : Field (Kroot T b) := inferInstance

noncomputable instance krootFiniteDimensional :
    FiniteDimensional (Kq T b) (Kroot T b) := by
  have hroot_int : IsIntegral (Kq T b) (candidateKRoot T b) :=
    (isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic (candidateKRoot T b)))
  exact IntermediateField.adjoin.finiteDimensional
    (K := Kq T b) (x := candidateKRoot T b) hroot_int

abbrev KRootCandidates : Type := {r : ACq T b // r ^ n2l (l := l) =
  algebraMap (Kq T b) (ACq T b) ((qVFamilyK T b).q)}

noncomputable def KRootMuAction
    (ζ : rootsOfUnity (n2l (l := l)) (ACq T b))
    (r : KRootCandidates T b) : KRootCandidates T b :=
  ⟨((ζ : (ACq T b)ˣ) : ACq T b) * r.1, by
    rw [mul_pow, r.2]
    have hζ : ((ζ : (ACq T b)ˣ) : ACq T b) ^ n2l (l := l) = 1 := by
      have h := ζ.property
      simpa using congrArg (fun u : (ACq T b)ˣ => (u : ACq T b)) h
    rw [hζ, one_mul]⟩

structure KrootCandidate where
  root : ACq T b
  root_pow : root ^ n2l (l := l) =
    algebraMap (Kq T b) (ACq T b) ((qVFamilyK T b).q)
  Kroot : IntermediateField (Kq T b) (ACq T b)
  Kroot_eq : Kroot = KrootField T b
  mu2lAction : rootsOfUnity (n2l (l := l)) (ACq T b) →
    KRootCandidates T b → KRootCandidates T b

noncomputable def krootCandidate : KrootCandidate T b where
  root := candidateKRoot T b
  root_pow := candidateKRoot_pow T b
  Kroot := KrootField T b
  Kroot_eq := rfl
  mu2lAction := KRootMuAction T b

-- Exact missing order/ramification control: the root is only in the
-- algebraic closure; no 2l | order_K statement and no root in Kq.
structure KrootOrderControlGap where
  root_in_completion : Prop
  twoL_dvd_order_K : (2 * l.value) ∣ (qVFamilyK T b).order
  root_valuation : Prop
  ramification_index_control : Prop

def KrootOrderControlGapRequired : Prop :=
  Nonempty (KrootOrderControlGap T b)

#check Kq
#check candidateKRoot
#check KrootField
#check krootFiniteDimensional
#check KRootMuAction
#check krootCandidate
#check KrootOrderControlGap

end LeanFormal.IUT.XiFPaper.S459KrootCandidateActual

end