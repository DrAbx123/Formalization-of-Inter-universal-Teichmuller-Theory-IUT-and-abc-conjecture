import tmp.sheaf.xif.paper.S346OrbifoldStructuralSheafActual
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

-- S355 candidate model only: quotient of algebraic-closure roots by mu_{2l}
-- no paper O^tri claim, no completion root, no fake.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S355OrbifoldRootStackCandidateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S330QVFamilyRootCardActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S346OrbifoldStructuralSheafActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev K (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type :=
  Completion (qVFamilyPlace T b)
abbrev AC (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type :=
  AlgebraicClosure (K T b)

def n : Nat := 2 * l.value

theorem n_pos : 0 < n (l := l) := by
  unfold n
  exact Nat.mul_pos (by norm_num) l.prime.pos

noncomputable def candidateRoot : AC T b :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (K T b) (AC T b) ((qVFamily T b).q)) (n_pos (l := l)))

theorem candidateRoot_pow :
    candidateRoot T b ^ n (l := l) =
      algebraMap (K T b) (AC T b) ((qVFamily T b).q) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (K T b) (AC T b) ((qVFamily T b).q)) (n_pos (l := l)))

abbrev CandidateRoots (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type := {r : AC T b // r ^ n (l := l) =
  algebraMap (K T b) (AC T b) ((qVFamily T b).q)}

noncomputable def candidateRootsAction (ζ : rootsOfUnity (n (l := l)) (AC T b))
    (r : CandidateRoots T b) : CandidateRoots T b :=
  ⟨((ζ : (AC T b)ˣ) : AC T b) * r.1, by
    rw [mul_pow, r.2]
    have hζ : ((ζ : (AC T b)ˣ) : AC T b) ^ n (l := l) = 1 := by
      have h := ζ.property
      simpa using congrArg (fun u : (AC T b)ˣ => (u : AC T b)) h
    rw [hζ, one_mul]⟩

noncomputable instance candidateRootsMulAction :
    MulAction (rootsOfUnity (n (l := l)) (AC T b)) (CandidateRoots T b) where
  smul := candidateRootsAction T b
  one_smul r := Subtype.ext (by change (1 : AC T b) * r.1 = r.1; rw [one_mul])
  mul_smul a c r := Subtype.ext (by change ((a : (AC T b)ˣ) : AC T b) * ((c : (AC T b)ˣ) : AC T b) * r.1 = ((a : (AC T b)ˣ) : AC T b) * (((c : (AC T b)ˣ) : AC T b) * r.1); rw [mul_assoc])

abbrev RootStackCandidate (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type :=
  MulAction.orbitRel.Quotient (rootsOfUnity (n (l := l)) (AC T b)) (CandidateRoots T b)

noncomputable def candidateRootSubtype : CandidateRoots T b :=
  ⟨candidateRoot T b, candidateRoot_pow T b⟩

noncomputable def rootClass : RootStackCandidate T b :=
  Quotient.mk (MulAction.orbitRel (rootsOfUnity (n (l := l)) (AC T b)) (CandidateRoots T b))
    (candidateRootSubtype T b)

instance rootStackSubsingleton : Subsingleton (RootStackCandidate T b) := by
  constructor
  intro x y
  refine Quotient.inductionOn x (fun r => ?_)
  refine Quotient.inductionOn y (fun s => ?_)
  apply Quotient.sound
  change MulAction.orbitRel (rootsOfUnity (n (l := l)) (AC T b)) (CandidateRoots T b) r s
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  have hq : algebraMap (K T b) (AC T b) ((qVFamily T b).q) ≠ 0 := by
    exact (map_ne_zero (algebraMap (K T b) (AC T b))).mpr (qVFamily T b).q_ne_zero
  have hr : r.1 ≠ 0 := by
    intro h
    have hpow := r.2
    rw [h, zero_pow (Nat.ne_of_gt (n_pos (l := l)))] at hpow
    exact hq hpow.symm
  have hs : s.1 ≠ 0 := by
    intro h
    have hpow := s.2
    rw [h, zero_pow (Nat.ne_of_gt (n_pos (l := l)))] at hpow
    exact hq hpow.symm
  have hratio : (r.1 / s.1) ^ n (l := l) = 1 := by
    rw [div_pow, r.2, s.2, div_self hq]
  let ζ : rootsOfUnity (n (l := l)) (AC T b) :=
    ⟨Units.mk0 (r.1 / s.1) (div_ne_zero hr hs), by
      ext
      rw [Units.val_pow_eq_pow_val]
      simp [hratio]⟩
  refine ⟨ζ, ?_⟩
  apply Subtype.ext
  change ((ζ : (AC T b)ˣ) : AC T b) * s.1 = r.1
  simp [ζ]
  field_simp [hs]

noncomputable instance rootStackMonoid : Monoid (RootStackCandidate T b) where
  mul _ _ := rootClass T b
  one := rootClass T b
  one_mul x := Subsingleton.elim _ _
  mul_one x := Subsingleton.elim _ _
  mul_assoc _ _ _ := Subsingleton.elim _ _

noncomputable def mu2lAction (ζ : rootsOfUnity (n (l := l)) (AC T b)) :
    RootStackCandidate T b → RootStackCandidate T b :=
  id

noncomputable def qSectionToCompletion (_ : RootStackCandidate T b) : K T b :=
  (qVFamily T b).q

-- Candidate spec for S346, explicitly not a paper O^tri claim.
noncomputable def candidateSpec :
    OrbifoldStructuralSheafCarrierSpec.{0} T b where
  carrier := RootStackCandidate T b
  monoid := rootStackMonoid T b
  qSection := rootClass T b
  rootSection := rootClass T b
  qSection_toCompletion := qSectionToCompletion T b
  qSection_toCompletion_q := rfl
  rootSection_pow := Subsingleton.elim _ _
  structuralSheafCondition := ∀ ζ, mu2lAction T b ζ = id

#check RootStackCandidate
#check rootClass
#check mu2lAction
#check candidateSpec

end LeanFormal.IUT.XiFPaper.S355OrbifoldRootStackCandidateActual

end