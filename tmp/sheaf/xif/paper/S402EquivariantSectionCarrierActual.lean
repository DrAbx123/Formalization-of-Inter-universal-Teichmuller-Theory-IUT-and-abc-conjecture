import tmp.sheaf.xif.paper.S392RootStackSectionMonoidActual
import Mathlib.Algebra.Ring.Parity

-- S402: attempt to tighten the S392 candidate to mu2l-equivariant sections.
-- The invariant submonoid is actual, but the delta injection is not invariant;
-- the missing injection is recorded exactly, and the candidate is marked failed.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S402EquivariantSectionCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S330QVFamilyRootCardActual
open LeanFormal.IUT.XiFPaper.S355OrbifoldRootStackCandidateActual
open LeanFormal.IUT.XiFPaper.S356RootStackActionGroupoidActual
open LeanFormal.IUT.XiFPaper.S392RootStackSectionMonoidActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def equivariantSections : Submonoid (SectionCarrier T b) where
  carrier := {f | ∀ (ζ : rootsOfUnity (n (l := l)) (AC T b)) (r : RootObj T b),
    f (ζ • r) = f r}
  one_mem' := by
    intro ζ r
    rfl
  mul_mem' := by
    intro f g hf hg ζ r
    simp only [Pi.mul_apply]
    rw [hf ζ r, hg ζ r]

abbrev EquivariantSectionCarrier : Type :=
  ↥(equivariantSections T b)

noncomputable def candidateRootSubtype_ne_zero :
    (candidateRootSubtype T b).1 ≠ 0 := by
  intro h
  have hpow := (candidateRootSubtype T b).2
  rw [h, zero_pow (Nat.ne_of_gt (n_pos (l := l)))] at hpow
  have hq : algebraMap (K T b) (AC T b) ((qVFamily T b).q) ≠ 0 := by
    exact (map_ne_zero (algebraMap (K T b) (AC T b))).mpr (qVFamily T b).q_ne_zero
  exact hq hpow.symm

noncomputable def negOneMu : rootsOfUnity (n (l := l)) (AC T b) :=
  ⟨(-1 : (AC T b)ˣ), by
    ext
    rw [Units.val_pow_eq_pow_val]
    exact Even.neg_one_pow ⟨l.value, by dsimp [n]; ring⟩⟩

theorem negOneMu_eq : (negOneMu T b : (AC T b)ˣ) = -1 := rfl

theorem negOneMu_smul_root_ne :
    negOneMu T b • rootObj T b ≠ rootObj T b := by
  intro h
  have hval := congrArg Subtype.val h
  change ((-1 : AC T b) * (candidateRootSubtype T b).1) =
    (candidateRootSubtype T b).1 at hval
  have h2 : ((-2 : AC T b) * (candidateRootSubtype T b).1) = 0 := by
    linear_combination hval
  have h2ne : (-2 : AC T b) ≠ 0 := by
    norm_num
  have hzero : (candidateRootSubtype T b).1 = 0 :=
    (mul_eq_zero.mp h2).resolve_left h2ne
  exact candidateRootSubtype_ne_zero T b hzero

theorem rootDelta_root_not_mem :
    rootDelta T b (rootObj T b) ∉ equivariantSections T b := by
  intro hmem
  have h := hmem (negOneMu T b) (rootObj T b)
  have hne := negOneMu_smul_root_ne T b
  have hl : rootDelta T b (rootObj T b) (negOneMu T b • rootObj T b) =
      (1 : Multiplicative ℤ) := by
    classical
    simp [rootDelta, hne]
  have hr : rootDelta T b (rootObj T b) (rootObj T b) =
      Multiplicative.ofAdd (1 : ℤ) := by
    classical
    simp [rootDelta]
  rw [hl, hr] at h
  exact ofAdd_one_ne_one h.symm

-- q/root sections in the invariant carrier, with value-based q-map.
noncomputable def oneEquivariantSection : EquivariantSectionCarrier T b :=
  ⟨1, by intro ζ r; rfl⟩

noncomputable def equivariantSectionToCompletion
    (f : EquivariantSectionCarrier T b) : Completion (qVFamilyPlace T b) :=
  (qVFamily T b).q ^
    ((Multiplicative.toAdd (f.1 (rootObj T b))).toNat + 1)

theorem oneEquivariantSection_toCompletion :
    equivariantSectionToCompletion T b (oneEquivariantSection T b) = (qVFamily T b).q := by
  simp [equivariantSectionToCompletion, oneEquivariantSection]

noncomputable def equivariantMu2lAction
    (_ : rootsOfUnity (n (l := l)) (AC T b))
    (f : EquivariantSectionCarrier T b) : EquivariantSectionCarrier T b := f

-- Exact obstruction: the canonical delta injection is not invariant.
structure EquivariantRootInjectionGap where
  rootToCarrier : RootObj T b → EquivariantSectionCarrier T b
  injective : Function.Injective rootToCarrier

def EquivariantRootInjectionGapRequired : Prop :=
  Nonempty (EquivariantRootInjectionGap T b)

theorem equivariantCandidateFails :
    rootDelta T b (rootObj T b) ∉ equivariantSections T b :=
  rootDelta_root_not_mem T b

#check EquivariantSectionCarrier
#check rootDelta_root_not_mem
#check equivariantCandidateFails
#check EquivariantRootInjectionGap

end LeanFormal.IUT.XiFPaper.S402EquivariantSectionCarrierActual

end