import tmp.sheaf.xif.paper.S1671ODSubmoduleActual
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Data.Fintype.Lattice

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1673ODSubmoduleConstructActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1664FmodODActual
open LeanFormal.IUT.XiFPaper.S1671ODSubmoduleActual

universe u

open scoped Pointwise

/-!
# S1673: actual O(-D) as a colon submodule of Fmod

This file fills the total/localization gap of `S1671ODSubmoduleData` without
`FractionalIdeal`, without a free lattice and without an abstract carrier.

For a bad place `P` (a finite place of `Fmod`) and the actual coefficient
`s1671Coefficient l b` (the order of the completed-DVR q-candidate at the
lifted place), the local pole-allowing piece is the general ideal quotient

  `P ^ (-coeff) = O_Fmod : P ^ coeff
                = {x : Fmod | x * P ^ coeff ≤ O_Fmod}`

implemented as `Submodule.div` of the image of the ideal `P ^ coeff` inside
`Fmod`.  The total is the finite intersection over the finite bad-place type
`Bad (S1280Selection l)`.  Localization is exactly the canonical completion
embedding `algebraMap Fmod (Completion v)`, applied to the underlying element
of the submodule.
-/

/-! ## 1. The per-place inverse `P ^ (-coeff)` -/

/-- The base field `Fmod` of the actual S1280 arithmetic data. -/
abbrev s1673K (l : PrimeGeFive) : Type :=
  (S1280Arithmetic l).Fmod

/-- The ring of integers `O_Fmod` of the actual S1280 arithmetic data. -/
abbrev s1673O (l : PrimeGeFive) : Type :=
  NumberField.RingOfIntegers (s1673K l)

/-- The actual ideal `P ^ coeff` attached to a bad place.  The exponent is
the order of `badPlaceQCandidate` (through `s1671Coefficient`), not an
arbitrary chosen integer. -/
noncomputable def s1673BadPlaceIdeal (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) : Ideal (s1673O l) :=
  b.1.maximalIdeal.asIdeal ^ (s1671Coefficient l b).toNat

/-- The image of `P ^ coeff` in the fraction field `Fmod`. -/
noncomputable def s1673BadPlacePowSubmodule (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) : Submodule (s1673O l) (s1673K l) :=
  Submodule.map (Algebra.linearMap (s1673O l) (s1673K l))
    (s1673BadPlaceIdeal l b)

/-- The actual local factor `P ^ (-coeff) = O : P ^ coeff`, i.e.
`{x : Fmod | x * P ^ coeff ≤ O}`.  This is the general ideal quotient
`Submodule.div`; no `FractionalIdeal` inverse is used. -/
noncomputable def s1673BadPlaceInverse (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) : Submodule (s1673O l) (s1673K l) :=
  (1 : Submodule (s1673O l) (s1673K l)) / s1673BadPlacePowSubmodule l b

/-- Membership in `P ^ (-coeff)` is exactly `x * P ^ coeff ≤ O`. -/
theorem s1673_mem_badPlaceInverse_iff (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) (x : s1673K l) :
    x ∈ s1673BadPlaceInverse l b ↔
      ∀ y ∈ s1673BadPlaceIdeal l b,
        x * algebraMap (s1673O l) (s1673K l) y ∈
          (1 : Submodule (s1673O l) (s1673K l)) := by
  rw [s1673BadPlaceInverse, Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro h y hy
    exact h _ (Submodule.mem_map_of_mem hy)
  · rintro h z hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    exact h y hy

/-- The same membership statement in the form `x • P ^ coeff ≤ O`. -/
theorem s1673_mem_badPlaceInverse_iff_smul (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) (x : s1673K l) :
    x ∈ s1673BadPlaceInverse l b ↔
      x • (s1673BadPlacePowSubmodule l b : Set (s1673K l)) ⊆
        ((1 : Submodule (s1673O l) (s1673K l)) : Set (s1673K l)) := by
  rw [s1673BadPlaceInverse, Submodule.mem_div_iff_smul_subset]

/-- The exponent is the actual q-candidate order. -/
theorem s1673Coefficient_toNat (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (s1671Coefficient l b).toNat =
      (badPlaceQCandidate (S1280Selection l) b).order := by
  simp [s1671Coefficient]

/-- The actual coefficient is positive, so `P ^ coeff` is a genuine
nonnegative pole order. -/
theorem s1673Coefficient_pos (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    0 < s1671Coefficient l b := by
  unfold s1671Coefficient
  exact_mod_cast badPlaceQCandidate_order_pos (S1280Selection l) b

/-- The ideal at every bad place is literally `P ^ order`, with the order of
the completed-DVR q-candidate. -/
@[simp] theorem s1673BadPlaceIdeal_eq_order (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    s1673BadPlaceIdeal l b =
      b.1.maximalIdeal.asIdeal ^
        (badPlaceQCandidate (S1280Selection l) b).order := by
  rw [s1673BadPlaceIdeal, s1673Coefficient_toNat]

/-! ## 2. The finite total over the bad places -/

/-- The actual total `O(-D)`: finite intersection of the local factors over
the finite bad-place index. -/
noncomputable def s1673Total (l : PrimeGeFive) :
    Submodule (s1673O l) (s1673K l) :=
  ⨅ b : Bad (S1280Selection l), s1673BadPlaceInverse l b

/-- Membership in the total is membership in every local factor. -/
theorem s1673_mem_total_iff (l : PrimeGeFive) (x : s1673K l) :
    x ∈ s1673Total l ↔
      ∀ b : Bad (S1280Selection l), x ∈ s1673BadPlaceInverse l b := by
  rw [s1673Total, Submodule.mem_iInf]

/-- The total is literally the finite intersection over `Finset.univ` of the
finite bad-place index. -/
theorem s1673Total_eq_finset_inf (l : PrimeGeFive) :
    s1673Total l = Finset.univ.inf (s1673BadPlaceInverse l) := by
  rw [s1673Total, Finset.inf_univ_eq_iInf]

/-- The bad-place index of the actual S1280 selection is a singleton, so the
finite intersection is the single actual local factor. -/
theorem s1673Total_eq_badPlaceInverse (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    s1673Total l = s1673BadPlaceInverse l b := by
  haveI : Subsingleton (Bad (S1280Selection l)) := S1280Bad_subsingleton l
  rw [s1673Total]
  refine le_antisymm (iInf_le _ b) ?_
  refine le_iInf fun b' => ?_
  have h : b' = b := Subsingleton.elim b' b
  rw [h]

/-- The actual bad place: the selected place above `5`. -/
noncomputable def s1673ActualBadPlace (l : PrimeGeFive) :
    Bad (S1280Selection l) :=
  ⟨S1280Place l, by
    rw [S1280Selection_V_mod_bad]
    exact Set.mem_singleton _⟩

@[simp] theorem s1673ActualBadPlace_val (l : PrimeGeFive) :
    (s1673ActualBadPlace l).1 = S1280Place l := rfl

/-- At the actual S1280 data, the total is exactly the single actual local
factor `P ^ (-coeff)`. -/
theorem s1673Total_eq_actualBadPlaceInverse (l : PrimeGeFive) :
    s1673Total l = s1673BadPlaceInverse l (s1673ActualBadPlace l) :=
  s1673Total_eq_badPlaceInverse l _

/-- The actual ideal `P ^ coeff` at the selected bad place. -/
noncomputable def s1673ActualIdeal (l : PrimeGeFive) : Ideal (s1673O l) :=
  s1673BadPlaceIdeal l (s1673ActualBadPlace l)

@[simp] theorem s1673ActualIdeal_eq (l : PrimeGeFive) :
    s1673ActualIdeal l =
      (S1280Place l).maximalIdeal.asIdeal ^
        (s1671Coefficient l (s1673ActualBadPlace l)).toNat :=
  rfl

/-- The actual exponent is the order of the completed-DVR q-candidate. -/
theorem s1673ActualIdeal_eq_order (l : PrimeGeFive) :
    s1673ActualIdeal l =
      (S1280Place l).maximalIdeal.asIdeal ^
        (badPlaceQCandidate (S1280Selection l)
          (s1673ActualBadPlace l)).order := by
  rw [s1673ActualIdeal_eq, s1673Coefficient_toNat]

/-- **Actual O(-D) characterization**: the total is exactly
`{x : Fmod | x * P ^ coeff ≤ O_Fmod}` at the actual selected place, with
`coeff` the q-candidate order. -/
theorem s1673_mem_total_iff_actual (l : PrimeGeFive) (x : s1673K l) :
    x ∈ s1673Total l ↔
      ∀ y ∈ s1673ActualIdeal l,
        x * algebraMap (s1673O l) (s1673K l) y ∈
          (1 : Submodule (s1673O l) (s1673K l)) := by
  rw [s1673Total_eq_actualBadPlaceInverse]
  exact s1673_mem_badPlaceInverse_iff l (s1673ActualBadPlace l) x

/-- Every local factor contains `O_Fmod`; in particular it is nonzero. -/
theorem s1673BadPlacePowSubmodule_le_one (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    s1673BadPlacePowSubmodule l b ≤
      (1 : Submodule (s1673O l) (s1673K l)) := by
  intro x hx
  obtain ⟨y, _hy, rfl⟩ := Submodule.mem_map.mp hx
  exact Submodule.mem_one.mpr ⟨y, rfl⟩

/-- `1 ∈ P ^ (-coeff)`: the pole-allowing factor contains the integers. -/
theorem s1673_one_mem_badPlaceInverse (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (1 : s1673K l) ∈ s1673BadPlaceInverse l b := by
  rw [s1673BadPlaceInverse, Submodule.one_mem_div]
  exact s1673BadPlacePowSubmodule_le_one l b

/-- The total is nonzero: it contains the unit section `1`. -/
theorem s1673_one_mem_total (l : PrimeGeFive) :
    (1 : s1673K l) ∈ s1673Total l := by
  rw [s1673_mem_total_iff]
  intro b
  exact s1673_one_mem_badPlaceInverse l b

theorem s1673Total_ne_bot (l : PrimeGeFive) :
    s1673Total l ≠ ⊥ := by
  intro h
  have h1 : (1 : s1673K l) ∈ (⊥ : Submodule (s1673O l) (s1673K l)) := by
    rw [← h]
    exact s1673_one_mem_total l
  rw [Submodule.mem_bot] at h1
  exact one_ne_zero h1

/-! ## 3. Localization and the S1671 structure -/

/-- Localization of a section is the canonical completion embedding
`Fmod → Completion v`, applied to the underlying field element. -/
noncomputable def s1673Localization (l : PrimeGeFive) :
    (v : NumberField.FinitePlace (s1673K l)) →
      s1673Total l → NumberFieldFinitePlace.Completion v :=
  fun v x =>
    algebraMap (s1673K l) (NumberFieldFinitePlace.Completion v)
      (x : s1673K l)

/-- The actual `S1671ODSubmoduleData`: the colon-submodule total together
with the canonical completion localization. -/
noncomputable def s1673ODSubmoduleData (l : PrimeGeFive) :
    S1671ODSubmoduleData l where
  total := s1673Total l
  localization := s1673Localization l

@[simp] theorem s1673ODSubmoduleData_total (l : PrimeGeFive) :
    (s1673ODSubmoduleData l).total = s1673Total l := rfl

theorem s1673Localization_apply (l : PrimeGeFive)
    (v : NumberField.FinitePlace (s1673K l)) (x : s1673Total l) :
    s1673Localization l v x =
      algebraMap (s1673K l) (NumberFieldFinitePlace.Completion v)
        (x : s1673K l) := rfl

theorem s1673ODSubmoduleData_localization_apply (l : PrimeGeFive)
    (v : NumberField.FinitePlace (s1673K l)) (x : s1673Total l) :
    (s1673ODSubmoduleData l).localization v x =
      algebraMap (s1673K l) (NumberFieldFinitePlace.Completion v)
        (x : s1673K l) := rfl

/-- The localization of a section only depends on its underlying element. -/
theorem s1673Localization_eq_algebraMap (l : PrimeGeFive)
    (v : NumberField.FinitePlace (s1673K l)) (x : s1673Total l) :
    (s1673ODSubmoduleData l).localization v x =
      algebraMap (s1673K l) (NumberFieldFinitePlace.Completion v)
        (x : s1673K l) :=
  rfl

end LeanFormal.IUT.XiFPaper.S1673ODSubmoduleConstructActual
end
