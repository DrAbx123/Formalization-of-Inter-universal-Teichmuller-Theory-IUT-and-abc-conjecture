import tmp.sheaf.xif.paper.S355OrbifoldRootStackCandidateActual
import Mathlib.Algebra.Torsor.Defs
/-! # S754: CandidateRoots is a Torsor for rootsOfUnity (2l) (AC T b)
Installs the actual Torsor instance using the root-ratio division.  This
replaces Classical.choose-based orbit reasoning by Equiv.smulConst. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
namespace LeanFormal.IUT.XiFPaper.S754CandidateRootsTorsorActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S355OrbifoldRootStackCandidateActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Nonzeroness of a candidate root. -/
theorem candidateRoots_ne_zero (r : CandidateRoots T b) : r.1 ≠ 0 := by
  intro h
  have hpow := r.2
  rw [h, zero_pow (Nat.ne_of_gt (n_pos (l := l)))] at hpow
  have hq : algebraMap (K T b) (AC T b) ((qVFamily T b).q) ≠ 0 :=
    (map_ne_zero (algebraMap (K T b) (AC T b))).mpr (qVFamily T b).q_ne_zero
  exact hq hpow.symm
/-- Root-ratio division in mu_{2l}. -/
noncomputable def candidateRootsSDiv (r s : CandidateRoots T b) :
    rootsOfUnity (n (l := l)) (AC T b) :=
  ⟨Units.mk0 (r.1 / s.1)
      (div_ne_zero (candidateRoots_ne_zero T b r)
        (candidateRoots_ne_zero T b s)), by
    ext
    rw [Units.val_pow_eq_pow_val]
    have hratio : (r.1 / s.1) ^ n (l := l) = 1 := by
      rw [div_pow, r.2, s.2, div_self (by
        have hq : algebraMap (K T b) (AC T b) ((qVFamily T b).q) ≠ 0 :=
          (map_ne_zero (algebraMap (K T b) (AC T b))).mpr (qVFamily T b).q_ne_zero
        exact hq)]
    simp [hratio]⟩
/-- Torsor instance on CandidateRoots. -/
noncomputable instance candidateRootsTorsor :
    Torsor (rootsOfUnity (n (l := l)) (AC T b)) (CandidateRoots T b) where
  nonempty := ⟨candidateRootSubtype T b⟩
  sdiv := candidateRootsSDiv T b
  sdiv_smul' r s := by
    apply Subtype.ext
    change ((candidateRootsSDiv T b r s : (AC T b)ˣ) : AC T b) * s.1 = r.1
    unfold candidateRootsSDiv
    simp only [Units.val_mk0]
    field_simp [candidateRoots_ne_zero T b s]
  smul_sdiv' ζ r := by
    apply Units.ext
    change (((((ζ : (AC T b)ˣ) : AC T b) * r.1) / r.1)) =
      ((ζ : (AC T b)ˣ) : AC T b)
    field_simp [candidateRoots_ne_zero T b r]
/-- Equiv.smulConst from the Torsor. -/
noncomputable def candidateRootsEquivSmulConst (r : CandidateRoots T b) :
    rootsOfUnity (n (l := l)) (AC T b) ≃ CandidateRoots T b :=
  Equiv.smulConst r
end LeanFormal.IUT.XiFPaper.S754CandidateRootsTorsorActual
