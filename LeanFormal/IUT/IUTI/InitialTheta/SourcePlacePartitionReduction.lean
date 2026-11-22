import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.IUTI.InitialTheta.SourceArithmeticPrelude
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceSelection
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier
import LeanFormal.IUT.IUTI.InitialTheta.ReductionPlacePartition
import LeanFormal.IUT.Foundations.Geometry.FinitePlaceDegreeSumBound
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegreeGlobal
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import Mathlib.Tactic

/-!
# D3/D4 reduction pass: the arithmetic place partition and the reduction clause

Source: IUT I, Definition 3.1(a)(b), with the notation of (e); the place
partition V(F) = V_non ⊔ V_arc, its bad/good split along the moduli places
V^bad_mod, and the stable/multiplicative/split reduction data with q-parameter
are read off the values `V_mod_bijection : V_mod ≃ V(F)` of the restriction
section.

Constructed here from `InitialThetaArithmeticData` plus the source selection
`SourcePlaceSelection` (the bad moduli set and its arithmetic fields):

* the finite/infinite index partition
  `Sum V^non_mod V^arc_mod ~ V(F)`, its bijectivity, cover, and pairwise
  disjointness;
* the section lifts of moduli places, the induced `PlacesAbove` elements, and
  the unconditional fibre degree bookkeeping (`e * f` sum equals the relative
  field degree, local degree above a residue characteristic bounded by the
  absolute degree);
* the residue-characteristic labels for the bad selection, with oddness, and
  the prime-strip labels (`RationalPrimePlace`, `FinitePrimePlace lower upper`);
* the valuation-theoretic q-candidate of each bad place from the completed
  discrete valuation ring, and a real-valued contracting parameter derived
  from its order;
* named cards for the stable/multiplicative/split reduction of the curve over
  the bad fibre and for the q-parameter order of Clause (c).

Boundary, stated explicitly:

* the existence of an `InitialThetaArithmeticData` is not asserted, in line
  with `InitialThetaArithmeticData` being an interface of `ArithmeticData.lean`;
* whether the curve has multiplicative reduction at the bad places is the
  content of `BadPlaceReductionCards` and stays open;
* the source q-parameter is a local uniformizer-type object of the curve; the
  parameter offered to the boundary interface here is the completed-DVR
  candidate `FinitePlaceQCandidate` (see
  `Foundations/NumberField/LocalQParameter.lean`), whose identification with a
  Tate parameter of the curve is not formalized.

Original-paper guidance used for the constructions: Definition 3.1(b) on the
stable reduction of the curve over all nonarchimedean places and the bad
moduli set; Definition 3.1(c) on the prime-to-l order of the q-parameter
orders; Definition 3.1(e) on the bijection V_mod ≃ V(F); Example 3.2(iv) on
the q-parameter of a multiplicative-reduction place.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace LeanFormal.IUT

noncomputable section

universe u v

/-! ## The finite/infinite carrier as a sum -/

namespace NumberFieldPlace

/-- The finite/infinite place carrier of a number field as a disjoint sum. -/
def sumEquiv (K : Type u) [Field K] [NumberField K] :
    Sum (NumberField.FinitePlace K) (NumberField.InfinitePlace K) ≃
      NumberFieldPlace K where
  toFun := fun s =>
    match s with
    | Sum.inl place => finite place
    | Sum.inr place => infinite place
  invFun := fun place =>
    match place with
    | finite place => Sum.inl place
    | infinite place => Sum.inr place
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro place
    cases place <;> rfl

@[simp] theorem sumEquiv_inl (K : Type u) [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) :
    sumEquiv K (Sum.inl place) = finite place :=
  rfl

@[simp] theorem sumEquiv_inr (K : Type u) [Field K] [NumberField K]
    (place : NumberField.InfinitePlace K) :
    sumEquiv K (Sum.inr place) = infinite place :=
  rfl

end NumberFieldPlace

/-! ## Finite-place restriction preserves the residue characteristic -/

namespace NumberFieldFinitePlace

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- Finite-place restriction preserves the residue characteristic. This is the
characteristic comparison behind the Clause (b) oddness condition on the bad
moduli places. -/
theorem residueCharacteristic_comap (place : NumberField.FinitePlace K) :
    residueCharacteristic (comap (k := k) place) =
      residueCharacteristic place := by
  let I : Ideal (NumberField.RingOfIntegers K) := place.maximalIdeal.asIdeal
  let J : Ideal (NumberField.RingOfIntegers k) :=
    I.comap (algebraMap (NumberField.RingOfIntegers k)
      (NumberField.RingOfIntegers K))
  have hJ : (comap (k := k) place).maximalIdeal.asIdeal = J := by
    exact comap_maximalIdeal place
  have hmemI :
      ((residueCharacteristic place : Nat) : NumberField.RingOfIntegers K) ∈
        I := by
    haveI : CharP (NumberField.RingOfIntegers K ⧸ I)
        (residueCharacteristic place) :=
      ringChar.of_eq rfl
    exact Ideal.natCast_mem_of_charP_quotient (residueCharacteristic place) I
  have hmemJ :
      ((residueCharacteristic place : Nat) : NumberField.RingOfIntegers k) ∈
        J := by
    have hmap :
        algebraMap (NumberField.RingOfIntegers k)
          (NumberField.RingOfIntegers K)
          ((residueCharacteristic place : Nat) :
            NumberField.RingOfIntegers k) ∈ I := by
      simpa only [map_natCast] using hmemI
    exact Ideal.mem_comap.mpr hmap
  have hpResidueRestricted :
      ((residueCharacteristic place : Nat) :
        ResidueField (comap (k := k) place)) = 0 := by
    have hmemMax :
        ((residueCharacteristic place : Nat) : NumberField.RingOfIntegers k) ∈
          (comap (k := k) place).maximalIdeal.asIdeal := by
      rw [hJ]
      exact hmemJ
    have hcast :
        ((residueCharacteristic place : Nat) :
          ResidueField (comap (k := k) place)) =
        Ideal.Quotient.mk (comap (k := k) place).maximalIdeal.asIdeal
          ((residueCharacteristic place : Nat) :
            NumberField.RingOfIntegers k) :=
      (map_natCast
        (Ideal.Quotient.mk (comap (k := k) place).maximalIdeal.asIdeal)
        (residueCharacteristic place)).symm
    rw [hcast]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmemMax
  have hdvd : residueCharacteristic (comap (k := k) place) ∣
      residueCharacteristic place := by
    haveI : CharP (ResidueField (comap (k := k) place))
        (residueCharacteristic (comap (k := k) place)) :=
      ringChar.of_eq rfl
    exact (CharP.cast_eq_zero_iff (ResidueField (comap (k := k) place))
      (residueCharacteristic (comap (k := k) place))
      (residueCharacteristic place)).mp hpResidueRestricted
  exact (Nat.prime_dvd_prime_iff_eq
    (CharP.prime_ringChar (ResidueField (comap (k := k) place)))
    (residueCharacteristic_prime place)).mp hdvd

end NumberFieldFinitePlace

/-! ## The arithmetic place partition of Definition 3.1(e) -/

namespace InitialThetaSource

namespace PlacePartitionReduction

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

/-- The selected places V(F) of the source restriction section. -/
abbrev Selected (P : SourcePlaceSelection A) :=
  {v : NumberFieldPlace A.K // v ∈ P.V}

/-- The bad moduli places V^bad_mod supplied by the source selection. -/
abbrev Bad (P : SourcePlaceSelection A) :=
  {p : NumberField.FinitePlace A.Fmod // p ∈ P.V_mod_bad}

/-- The finite index-to-place map of the Definition 3.1(e) bijection. -/
def finiteToV (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) : Selected P :=
  P.V_mod_bijection (NumberFieldPlace.finite p)

/-- The infinite index-to-place map of the Definition 3.1(e) bijection. -/
def infiniteToV (P : SourcePlaceSelection A)
    (v : NumberField.InfinitePlace A.Fmod) : Selected P :=
  P.V_mod_bijection (NumberFieldPlace.infinite v)

/-- The Definition 3.1(e) bijection V^non_mod ⊔ V^arc_mod ≃ V(F). -/
def kindEquiv (P : SourcePlaceSelection A) :
    Sum (NumberField.FinitePlace A.Fmod) (NumberField.InfinitePlace A.Fmod) ≃
      Selected P :=
  (NumberFieldPlace.sumEquiv A.Fmod).trans P.V_mod_bijection

@[simp] theorem kindEquiv_inl (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    kindEquiv P (Sum.inl p) = finiteToV P p :=
  rfl

@[simp] theorem kindEquiv_inr (P : SourcePlaceSelection A)
    (v : NumberField.InfinitePlace A.Fmod) :
    kindEquiv P (Sum.inr v) = infiniteToV P v :=
  rfl

theorem kindEquiv_bijective (P : SourcePlaceSelection A) :
    Function.Bijective (kindEquiv P) :=
  (kindEquiv P).bijective

theorem kindEquiv_injective (P : SourcePlaceSelection A) :
    Function.Injective (kindEquiv P) :=
  (kindEquiv P).injective

theorem kindEquiv_surjective (P : SourcePlaceSelection A) :
    Function.Surjective (kindEquiv P) :=
  (kindEquiv P).surjective

theorem selected_kind_cover (P : SourcePlaceSelection A) (w : Selected P) :
    (∃ p : NumberField.FinitePlace A.Fmod, finiteToV P p = w) ∨
      (∃ s : NumberField.InfinitePlace A.Fmod, infiniteToV P s = w) := by
  obtain ⟨u, hu⟩ := (kindEquiv P).surjective w
  cases u with
  | inl p =>
      exact Or.inl ⟨p, by rw [← kindEquiv_inl]; exact hu⟩
  | inr s =>
      exact Or.inr ⟨s, by rw [← kindEquiv_inr]; exact hu⟩

theorem finiteToV_ne_infiniteToV (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod)
    (s : NumberField.InfinitePlace A.Fmod) :
    finiteToV P p ≠ infiniteToV P s := by
  intro h
  have h' : kindEquiv P (Sum.inl p) = kindEquiv P (Sum.inr s) := by
    rw [kindEquiv_inl, kindEquiv_inr]
    exact h
  exact Sum.inl_ne_inr ((kindEquiv P).injective h')

theorem finiteToV_range_disjoint (P : SourcePlaceSelection A) :
    Disjoint (Set.range (finiteToV P)) (Set.range (infiniteToV P)) := by
  rw [Set.disjoint_left]
  rintro w ⟨p, rfl⟩ ⟨s, hs⟩
  exact finiteToV_ne_infiniteToV P p s hs.symm

theorem finiteToV_comap (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    NumberFieldPlace.comap (k := A.Fmod) (finiteToV P p).1 =
      NumberFieldPlace.finite p := by
  have h := P.V_place_comap (P.V_mod_bijection (NumberFieldPlace.finite p))
  have hleft := P.selected_equiv_left_inverse (NumberFieldPlace.finite p)
  rw [hleft] at h
  exact h

theorem infiniteToV_comap (P : SourcePlaceSelection A)
    (v : NumberField.InfinitePlace A.Fmod) :
    NumberFieldPlace.comap (k := A.Fmod) (infiniteToV P v).1 =
      NumberFieldPlace.infinite v := by
  have h := P.V_place_comap (P.V_mod_bijection (NumberFieldPlace.infinite v))
  have hleft := P.selected_equiv_left_inverse (NumberFieldPlace.infinite v)
  rw [hleft] at h
  exact h

theorem finiteToV_is_finite (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    NumberFieldPlace.IsFinite (finiteToV P p).1 :=
  P.selected_finite_places_nonempty p

theorem infiniteToV_is_infinite (P : SourcePlaceSelection A)
    (s : NumberField.InfinitePlace A.Fmod) :
    NumberFieldPlace.IsInfinite (infiniteToV P s).1 :=
  P.selected_infinite_places_arc s

theorem finiteToV_mem_V_non (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) : finiteToV P p ∈ P.V_non :=
  P.selected_finite_places_nonempty p

theorem infiniteToV_mem_V_arc (P : SourcePlaceSelection A)
    (s : NumberField.InfinitePlace A.Fmod) : infiniteToV P s ∈ P.V_arc :=
  P.selected_infinite_places_arc s

theorem selected_kind_partition (P : SourcePlaceSelection A) (w : Selected P) :
    (w ∈ P.V_non ∨ w ∈ P.V_arc) ∧
      ¬ (w ∈ P.V_non ∧ w ∈ P.V_arc) := by
  constructor
  · have hcover := congrArg (fun s => w ∈ s) P.V_non_or_arc_cover
    simpa [Set.mem_union] using hcover.mpr trivial
  · rintro ⟨hnon, harc⟩
    exact Set.disjoint_left.mp P.V_non_or_arc_disjoint hnon harc

/-! ## Section lifts of moduli places and fibre degree bookkeeping -/

theorem sectionFiniteLift_lift_exists (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    ∃ q : NumberField.FinitePlace A.K,
      P.V_section.lift (NumberFieldPlace.finite p) =
          NumberFieldPlace.finite q ∧
        NumberFieldFinitePlace.comap q = p := by
  have hComap := P.V_section.comap_lift (NumberFieldPlace.finite p)
  cases hLift : P.V_section.lift (NumberFieldPlace.finite p) with
  | finite q =>
      refine ⟨q, rfl, ?_⟩
      rw [hLift] at hComap
      exact NumberFieldPlace.finite.inj
        (by simpa only [NumberFieldPlace.comap_finite] using hComap)
  | infinite q =>
      exfalso
      rw [hLift] at hComap
      simp only [NumberFieldPlace.comap_infinite] at hComap
      exact (by cases hComap)

/-- The section lift of a finite moduli place, as a place of K. -/
def sectionFiniteLift (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) : NumberField.FinitePlace A.K :=
  Classical.choose (sectionFiniteLift_lift_exists P p)

theorem sectionFiniteLift_lift (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    P.V_section.lift (NumberFieldPlace.finite p) =
      NumberFieldPlace.finite (sectionFiniteLift P p) :=
  (Classical.choose_spec (sectionFiniteLift_lift_exists P p)).1

theorem sectionFiniteLift_comap (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    NumberFieldFinitePlace.comap (sectionFiniteLift P p) = p :=
  (Classical.choose_spec (sectionFiniteLift_lift_exists P p)).2

theorem sectionInfiniteLift_lift_exists (P : SourcePlaceSelection A)
    (v : NumberField.InfinitePlace A.Fmod) :
    ∃ w : NumberField.InfinitePlace A.K,
      P.V_section.lift (NumberFieldPlace.infinite v) =
          NumberFieldPlace.infinite w ∧
        w.comap (algebraMap A.Fmod A.K) = v := by
  have hComap := P.V_section.comap_lift (NumberFieldPlace.infinite v)
  cases hLift : P.V_section.lift (NumberFieldPlace.infinite v) with
  | finite q =>
      exfalso
      rw [hLift] at hComap
      simp only [NumberFieldPlace.comap_finite] at hComap
      exact (by cases hComap)
  | infinite w =>
      refine ⟨w, rfl, ?_⟩
      rw [hLift] at hComap
      exact NumberFieldPlace.infinite.inj
        (by simpa only [NumberFieldPlace.comap_infinite] using hComap)

/-- The section lift of an infinite moduli place, as a place of K. -/
def sectionInfiniteLift (P : SourcePlaceSelection A)
    (v : NumberField.InfinitePlace A.Fmod) :
    NumberField.InfinitePlace A.K :=
  Classical.choose (sectionInfiniteLift_lift_exists P v)

theorem sectionInfiniteLift_lift (P : SourcePlaceSelection A)
    (v : NumberField.InfinitePlace A.Fmod) :
    P.V_section.lift (NumberFieldPlace.infinite v) =
      NumberFieldPlace.infinite (sectionInfiniteLift P v) :=
  (Classical.choose_spec (sectionInfiniteLift_lift_exists P v)).1

theorem sectionInfiniteLift_comap (P : SourcePlaceSelection A)
    (v : NumberField.InfinitePlace A.Fmod) :
    (sectionInfiniteLift P v).comap (algebraMap A.Fmod A.K) = v :=
  (Classical.choose_spec (sectionInfiniteLift_lift_exists P v)).2

theorem finiteToV_eq_finite_lift (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    (finiteToV P p).1 = NumberFieldPlace.finite (sectionFiniteLift P p) := by
  have h : (finiteToV P p).1 =
      P.V_section.lift (NumberFieldPlace.finite p) := rfl
  rw [h, sectionFiniteLift_lift P p]

theorem infiniteToV_eq_infinite_lift (P : SourcePlaceSelection A)
    (v : NumberField.InfinitePlace A.Fmod) :
    (infiniteToV P v).1 =
      NumberFieldPlace.infinite (sectionInfiniteLift P v) := by
  have h : (infiniteToV P v).1 =
      P.V_section.lift (NumberFieldPlace.infinite v) := rfl
  rw [h, sectionInfiniteLift_lift P v]

/-- The section-selected K-place above a moduli place, as an element of the
Definition 3.1(e) fibre of restriction. -/
def sectionPlaceAbove (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    NumberFieldFinitePlace.PlacesAbove (K := A.K) p :=
  ⟨sectionFiniteLift P p, sectionFiniteLift_comap P p⟩

@[simp] theorem sectionPlaceAbove_val (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    (sectionPlaceAbove P p).1 = sectionFiniteLift P p :=
  rfl

theorem moduliPlace_fiber_nonempty (p : NumberField.FinitePlace A.Fmod) :
    ∃ w : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) w = p :=
  NumberFieldFinitePlace.comap_surjective (k := A.Fmod) (K := A.F) p

theorem badPlaceAbove_exists (P : SourcePlaceSelection A) :
    ∃ w : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad := by
  obtain ⟨p, hp⟩ := P.V_mod_bad_nonempty
  obtain ⟨w, hw⟩ := moduliPlace_fiber_nonempty (A := A) p
  exact ⟨w, by rw [hw]; exact hp⟩

theorem sum_relativeCompletionDegree_sectionPlaceAbove
    (P : SourcePlaceSelection A) (p : NumberField.FinitePlace A.Fmod) :
    (∑ u : NumberFieldFinitePlace.PlacesAbove (K := A.K) p,
      NumberFieldFinitePlace.relativeCompletionDegree (k := A.Fmod) u.1) =
      Module.finrank A.Fmod A.K :=
  NumberFieldFinitePlace.sum_relativeCompletionDegree_eq_fieldDegree
    (k := A.Fmod) (K := A.K) p

theorem relativeCompletionDegree_sectionFiniteLift_le
    (P : SourcePlaceSelection A) (p : NumberField.FinitePlace A.Fmod) :
    NumberFieldFinitePlace.relativeCompletionDegree (k := A.Fmod)
      (sectionFiniteLift P p) ≤ Module.finrank A.Fmod A.K := by
  have hsum := sum_relativeCompletionDegree_sectionPlaceAbove (A := A) P p
  have hle : NumberFieldFinitePlace.relativeCompletionDegree (k := A.Fmod)
        (sectionPlaceAbove P p).1 ≤
      ∑ u : NumberFieldFinitePlace.PlacesAbove (K := A.K) p,
        NumberFieldFinitePlace.relativeCompletionDegree (k := A.Fmod) u.1 :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun u : NumberFieldFinitePlace.PlacesAbove (K := A.K) p =>
        NumberFieldFinitePlace.relativeCompletionDegree (k := A.Fmod) u.1)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (sectionPlaceAbove P p))
  rw [hsum] at hle
  exact hle

theorem residueLocalDegree_sectionFiniteLift_le
    (P : SourcePlaceSelection A) (p : NumberField.FinitePlace A.Fmod) :
    NumberFieldFinitePlace.residueLocalDegree (sectionFiniteLift P p) ≤
      Module.finrank ℚ A.K := by
  have h := NumberFieldFinitePlace.sum_residueLocalDegree_filter_le
    (S := ({sectionFiniteLift P p} : Finset (NumberField.FinitePlace A.K)))
    (q := NumberFieldFinitePlace.residueCharacteristic (sectionFiniteLift P p))
  rw [Finset.filter_singleton, if_pos rfl, Finset.sum_singleton] at h
  exact h

theorem residueCharacteristic_sectionFiniteLift (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    NumberFieldFinitePlace.residueCharacteristic (sectionFiniteLift P p) =
      NumberFieldFinitePlace.residueCharacteristic p := by
  rw [← NumberFieldFinitePlace.residueCharacteristic_comap
    (k := A.Fmod) (K := A.K) (sectionFiniteLift P p)]
  exact congrArg NumberFieldFinitePlace.residueCharacteristic
    (sectionFiniteLift_comap P p)

theorem selectedNonempty (P : SourcePlaceSelection A) : Nonempty (Selected P) := by
  obtain ⟨p, _hp⟩ := P.V_mod_bad_nonempty
  exact ⟨finiteToV P p⟩

/-! ## The place-partition carrier bundled with its compatibility -/

/-- The Definition 3.1(e) place-partition carrier: index maps, the section
lifts, and their compatibility with restriction. -/
structure ArithmeticPlacePartition (P : SourcePlaceSelection A) where
  finiteToV : NumberField.FinitePlace A.Fmod → Selected P
  infiniteToV : NumberField.InfinitePlace A.Fmod → Selected P
  kindEquiv : Sum (NumberField.FinitePlace A.Fmod)
    (NumberField.InfinitePlace A.Fmod) ≃ Selected P
  kindEquiv_inl_apply : ∀ p, kindEquiv (Sum.inl p) = finiteToV p
  kindEquiv_inr_apply : ∀ v, kindEquiv (Sum.inr v) = infiniteToV v
  sectionFiniteLift : NumberField.FinitePlace A.Fmod →
    NumberField.FinitePlace A.K
  sectionInfiniteLift : NumberField.InfinitePlace A.Fmod →
    NumberField.InfinitePlace A.K
  finiteToV_eq_finite : ∀ p,
    (finiteToV p).1 = NumberFieldPlace.finite (sectionFiniteLift p)
  infiniteToV_eq_infinite : ∀ v,
    (infiniteToV v).1 = NumberFieldPlace.infinite (sectionInfiniteLift v)
  finite_moduli_compatibility : ∀ p,
    NumberFieldFinitePlace.comap (sectionFiniteLift p) = p
  infinite_moduli_compatibility : ∀ v,
    (sectionInfiniteLift v).comap (algebraMap A.Fmod A.K) = v

namespace ArithmeticPlacePartition

variable {P : SourcePlaceSelection A}

theorem kindEquiv_bijective (X : ArithmeticPlacePartition P) :
    Function.Bijective X.kindEquiv :=
  X.kindEquiv.bijective

theorem finiteToV_eq_finite_lift (X : ArithmeticPlacePartition P)
    (p : NumberField.FinitePlace A.Fmod) :
    (X.finiteToV p).1 = NumberFieldPlace.finite (X.sectionFiniteLift p) :=
  X.finiteToV_eq_finite p

theorem infiniteToV_eq_infinite_lift (X : ArithmeticPlacePartition P)
    (v : NumberField.InfinitePlace A.Fmod) :
    (X.infiniteToV v).1 =
      NumberFieldPlace.infinite (X.sectionInfiniteLift v) :=
  X.infiniteToV_eq_infinite v

end ArithmeticPlacePartition

def arithmeticPlacePartition (P : SourcePlaceSelection A) :
    ArithmeticPlacePartition P where
  finiteToV := finiteToV P
  infiniteToV := infiniteToV P
  kindEquiv := kindEquiv P
  kindEquiv_inl_apply := fun p => kindEquiv_inl P p
  kindEquiv_inr_apply := fun v => kindEquiv_inr P v
  sectionFiniteLift := sectionFiniteLift P
  sectionInfiniteLift := sectionInfiniteLift P
  finiteToV_eq_finite := fun p => finiteToV_eq_finite_lift P p
  infiniteToV_eq_infinite := fun v => infiniteToV_eq_infinite_lift P v
  finite_moduli_compatibility := fun p => sectionFiniteLift_comap P p
  infinite_moduli_compatibility := fun v => sectionInfiniteLift_comap P v

/-! ## Interface identity with the arithmetic prelude -/

theorem V_section_eq_prelude (P : SourcePlaceSelection A) :
    P.V_section = (SourceArithmeticPrelude.canonical A).placeSection :=
  rfl

theorem V_eq_prelude_selected (P : SourcePlaceSelection A) :
    P.V = (SourceArithmeticPrelude.canonical A).selectedPlaces :=
  rfl

theorem V_mod_bijection_eq_prelude (P : SourcePlaceSelection A) :
    P.V_mod_bijection = (SourceArithmeticPrelude.canonical A).selectedEquiv :=
  rfl

/-! ## The bad selection inside V(F) -/

def badIncluded (P : SourcePlaceSelection A) (b : Bad P) : Selected P :=
  finiteToV P b.1

theorem badIncluded_mem_V_bad (P : SourcePlaceSelection A) (b : Bad P) :
    badIncluded P b ∈ P.V_bad :=
  P.selected_bad_place_mem b.1 b.2

theorem badIncluded_is_finite (P : SourcePlaceSelection A) (b : Bad P) :
    NumberFieldPlace.IsFinite (badIncluded P b).1 :=
  finiteToV_is_finite P b.1

theorem badIncluded_residueCharacteristic_odd (P : SourcePlaceSelection A)
    (b : Bad P) :
    Odd (NumberFieldFinitePlace.residueCharacteristic
      (sectionFiniteLift P b.1)) := by
  rw [residueCharacteristic_sectionFiniteLift P b.1]
  exact P.V_mod_bad_odd_residue_characteristic b.1 b.2

theorem finiteToV_mem_V_bad_iff (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    finiteToV P p ∈ P.V_bad ↔ p ∈ P.V_mod_bad := by
  rw [P.V_bad_finite_spec (finiteToV P p)]
  have hleft : P.V_mod_bijection.symm (finiteToV P p) =
      NumberFieldPlace.finite p := by
    change P.V_mod_bijection.symm
        (P.V_mod_bijection (NumberFieldPlace.finite p)) =
      NumberFieldPlace.finite p
    exact P.V_mod_bijection.left_inv (NumberFieldPlace.finite p)
  rw [hleft]
  constructor
  · rintro ⟨q, hq, hqeq⟩
    have hqp : q = p := NumberFieldPlace.finite.inj hqeq
    rw [hqp] at hq
    exact hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem finiteToV_mem_V_good_iff (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    finiteToV P p ∈ P.V_good ↔ p ∉ P.V_mod_bad := by
  rw [P.V_good_spec (finiteToV P p)]
  have hleft : P.V_mod_bijection.symm (finiteToV P p) =
      NumberFieldPlace.finite p := by
    change P.V_mod_bijection.symm
        (P.V_mod_bijection (NumberFieldPlace.finite p)) =
      NumberFieldPlace.finite p
    exact P.V_mod_bijection.left_inv (NumberFieldPlace.finite p)
  rw [hleft]
  constructor
  · intro hnot hp
    exact hnot ⟨p, hp, rfl⟩
  · rintro hp ⟨q, hq, hqeq⟩
    have hqp : q = p := NumberFieldPlace.finite.inj hqeq
    rw [hqp] at hq
    exact hp hq

/-! ## Residue-characteristic and prime-strip labels -/

/-- The Clause (b) residue-characteristic label of a place. -/
def placeResidueLabel (place : NumberFieldPlace A.K) : Nat :=
  match place with
  | NumberFieldPlace.finite p =>
      NumberFieldFinitePlace.residueCharacteristic p
  | NumberFieldPlace.infinite _ => 0

def selectedResidueLabel (P : SourcePlaceSelection A) (w : Selected P) : Nat :=
  placeResidueLabel w.1

def badResidueLabel (P : SourcePlaceSelection A) (b : Bad P) : Nat :=
  NumberFieldFinitePlace.residueCharacteristic b.1

theorem selectedResidueLabel_finiteToV (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    selectedResidueLabel P (finiteToV P p) =
      NumberFieldFinitePlace.residueCharacteristic p := by
  have hLift := sectionFiniteLift_lift P p
  change placeResidueLabel
      (P.V_section.lift (NumberFieldPlace.finite p)) =
    NumberFieldFinitePlace.residueCharacteristic p
  rw [hLift]
  change NumberFieldFinitePlace.residueCharacteristic (sectionFiniteLift P p) =
    NumberFieldFinitePlace.residueCharacteristic p
  exact residueCharacteristic_sectionFiniteLift P p

theorem badResidueLabel_compatible (P : SourcePlaceSelection A) (b : Bad P) :
    selectedResidueLabel P (badIncluded P b) = badResidueLabel P b := by
  change selectedResidueLabel P (finiteToV P b.1) =
    NumberFieldFinitePlace.residueCharacteristic b.1
  exact selectedResidueLabel_finiteToV P b.1

theorem badResidueLabel_prime (P : SourcePlaceSelection A) (b : Bad P) :
    Nat.Prime (badResidueLabel P b) :=
  NumberFieldFinitePlace.residueCharacteristic_prime b.1

theorem badResidueLabel_odd (P : SourcePlaceSelection A) (b : Bad P) :
    Odd (badResidueLabel P b) :=
  P.V_mod_bad_odd_residue_characteristic b.1 b.2

def badStripLabel (P : SourcePlaceSelection A) (b : Bad P) :
    RationalPrimePlace :=
  ⟨badResidueLabel P b, badResidueLabel_prime P b⟩

def badFiniteStripIndex (P : SourcePlaceSelection A) (lower upper : Nat)
    (hbound : ∀ b : Bad P, lower ≤ badResidueLabel P b ∧
      badResidueLabel P b ≤ upper)
    (b : Bad P) : FinitePrimePlace lower upper :=
  ⟨badResidueLabel P b, ⟨(hbound b).1, (hbound b).2,
    badResidueLabel_prime P b⟩⟩

theorem badFiniteStripIndex_toRational (P : SourcePlaceSelection A)
    (lower upper : Nat)
    (hbound : ∀ b : Bad P, lower ≤ badResidueLabel P b ∧
      badResidueLabel P b ≤ upper)
    (b : Bad P) :
    (badFiniteStripIndex P lower upper hbound b).toRationalPrimePlace =
      badStripLabel P b :=
  Subtype.ext rfl

/-! ## D3 assembly: the source place partition -/

/-- The D3 assembly into the Theorem 3.11 source boundary: the selected
places, the bad moduli index, and the residue-characteristic labels. The
finiteness of the bad index is the source's finiteness of V^bad_mod. -/
def toSourcePlacePartition (P : SourcePlaceSelection A) [Fintype (Bad P)] :
    Theorem311Source.SourcePlacePartition (Selected P) (Bad P) where
  badIncluded := badIncluded P
  selectedNonempty := selectedNonempty P
  badFinite := inferInstance
  selectedLabel := selectedResidueLabel P
  badLabel := badResidueLabel P
  badLabel_compatible := badResidueLabel_compatible P

@[simp] theorem toSourcePlacePartition_badIncluded (P : SourcePlaceSelection A)
    [Fintype (Bad P)] (b : Bad P) :
    (toSourcePlacePartition P).badIncluded b = badIncluded P b :=
  rfl

@[simp] theorem toSourcePlacePartition_selectedLabel
    (P : SourcePlaceSelection A) [Fintype (Bad P)] (w : Selected P) :
    (toSourcePlacePartition P).selectedLabel w = selectedResidueLabel P w :=
  rfl

@[simp] theorem toSourcePlacePartition_badLabel (P : SourcePlaceSelection A)
    [Fintype (Bad P)] (b : Bad P) :
    (toSourcePlacePartition P).badLabel b = badResidueLabel P b :=
  rfl

/-! ## The valuation-theoretic q-candidate at a bad place -/

def badPlaceQCandidate (P : SourcePlaceSelection A) (b : Bad P) :
    NumberFieldFinitePlace.FinitePlaceQCandidate (sectionFiniteLift P b.1) :=
  Classical.choice (NumberFieldFinitePlace.finitePlaceQCandidate_nonempty
    (sectionFiniteLift P b.1))

theorem badPlaceQCandidate_q_ne_zero (P : SourcePlaceSelection A) (b : Bad P) :
    (badPlaceQCandidate P b).q ≠ 0 :=
  (badPlaceQCandidate P b).q_ne_zero

theorem badPlaceQCandidate_valuation_lt_one (P : SourcePlaceSelection A)
    (b : Bad P) :
    (Valued.v (badPlaceQCandidate P b).q : WithZero (Multiplicative Int)) < 1 :=
  (badPlaceQCandidate P b).valuation_lt_one

theorem badPlaceQCandidate_order_pos (P : SourcePlaceSelection A) (b : Bad P) :
    0 < (badPlaceQCandidate P b).order :=
  (badPlaceQCandidate P b).order_pos

def badPlaceQCandidate_pow (P : SourcePlaceSelection A) (b : Bad P)
    (n : Nat) (hn : 0 < n) :
    NumberFieldFinitePlace.FinitePlaceQCandidate (sectionFiniteLift P b.1) :=
  (badPlaceQCandidate P b).pow n hn

@[simp] theorem badPlaceQCandidate_pow_q (P : SourcePlaceSelection A)
    (b : Bad P) (n : Nat) (hn : 0 < n) :
    (badPlaceQCandidate_pow P b n hn).q = (badPlaceQCandidate P b).q ^ n :=
  rfl

theorem sectionFiniteLift_completionResidueField_charP
    (P : SourcePlaceSelection A) (p : NumberField.FinitePlace A.Fmod) :
    CharP (NumberFieldFinitePlace.CompletionResidueField
        (sectionFiniteLift P p))
      (NumberFieldFinitePlace.residueCharacteristic (sectionFiniteLift P p)) :=
  NumberFieldFinitePlace.charP_completionResidueField (sectionFiniteLift P p)

/-- The real contracting parameter attached to a bad place, derived from the
order of the completed-DVR q-candidate. It is a stand-in for the Tate
q-parameter of the curve, whose identification is not formalized. -/
def badPlaceQProxy (P : SourcePlaceSelection A) (b : Bad P) : Real :=
  ((NumberFieldFinitePlace.residueCharacteristic b.1 : Nat) : Real)⁻¹ ^
    (badPlaceQCandidate P b).order

theorem badPlaceQProxy_nonneg (P : SourcePlaceSelection A) (b : Bad P) :
    0 ≤ badPlaceQProxy P b :=
  pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _

theorem badPlaceQProxy_lt_one (P : SourcePlaceSelection A) (b : Bad P) :
    badPlaceQProxy P b < 1 := by
  have hbase_nonneg : 0 ≤
      ((NumberFieldFinitePlace.residueCharacteristic b.1 : Nat) : Real)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hbase_lt_one :
      ((NumberFieldFinitePlace.residueCharacteristic b.1 : Nat) : Real)⁻¹ <
        1 := by
    apply inv_lt_one_of_one_lt₀
    have htwo : (2 : Real) ≤
        ((NumberFieldFinitePlace.residueCharacteristic b.1 : Nat) : Real) := by
      exact_mod_cast
        (NumberFieldFinitePlace.residueCharacteristic_prime b.1).two_le
    linarith
  exact pow_lt_one₀ hbase_nonneg hbase_lt_one
    (Nat.ne_of_gt (badPlaceQCandidate_order_pos P b))

theorem badPlaceQProxy_norm_lt_one (P : SourcePlaceSelection A) (b : Bad P) :
    ‖badPlaceQProxy P b‖ < 1 := by
  rw [Real.norm_of_nonneg (badPlaceQProxy_nonneg P b)]
  exact badPlaceQProxy_lt_one P b

theorem badPlaceQProxy_ne_zero (P : SourcePlaceSelection A) (b : Bad P) :
    badPlaceQProxy P b ≠ 0 := by
  have hbase :
      ((NumberFieldFinitePlace.residueCharacteristic b.1 : Nat) : Real)⁻¹ ≠
        0 :=
    inv_ne_zero (by
      exact_mod_cast
        (NumberFieldFinitePlace.residueCharacteristic_prime b.1).ne_zero)
  exact pow_ne_zero _ hbase

theorem badPlaceQProxy_ne_one (P : SourcePlaceSelection A) (b : Bad P) :
    badPlaceQProxy P b ≠ 1 := by
  intro h
  have hlt := badPlaceQProxy_norm_lt_one P b
  rw [h, norm_one] at hlt
  exact lt_irrefl 1 hlt

/-- The valuation-theoretic q-candidate at an F-place of the curve field. -/
def fiberQCandidate (w : NumberField.FinitePlace A.F) :
    NumberFieldFinitePlace.FinitePlaceQCandidate w :=
  Classical.choice (NumberFieldFinitePlace.finitePlaceQCandidate_nonempty w)

theorem fiberQCandidate_q_ne_zero (w : NumberField.FinitePlace A.F) :
    (fiberQCandidate w).q ≠ 0 :=
  (fiberQCandidate w).q_ne_zero

theorem fiberQCandidate_valuation_lt_one (w : NumberField.FinitePlace A.F) :
    (Valued.v (fiberQCandidate w).q : WithZero (Multiplicative Int)) < 1 :=
  (fiberQCandidate w).valuation_lt_one

/-! ## D4 named cards and conditional assembly -/

/-- Clause (b) reduction cards: the curve has stable, multiplicative, and
split multiplicative reduction at every F-place above a bad moduli place.
This is the honest remaining arithmetic gap behind Definition 3.1(b). -/
structure BadPlaceReductionCards (P : SourcePlaceSelection A) where
  stableReduction : ∀ w : NumberField.FinitePlace A.F,
    NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad →
      A.curve.HasStableReductionAt w
  multiplicativeReduction : ∀ w : NumberField.FinitePlace A.F,
    NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad →
      A.curve.HasMultiplicativeReductionAt w
  splitMultiplicativeReduction : ∀ w : NumberField.FinitePlace A.F,
    NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad →
      A.curve.HasSplitMultiplicativeReductionAt w

/-- Clause (c) arithmetic cards: coprimality of the bad residue
characteristics with l, and the prime-to-l orders of the source q-parameter. -/
structure BadPlaceQParameterCards (P : SourcePlaceSelection A) where
  badResidueCharacteristic_primeToL : ∀ p : NumberField.FinitePlace A.Fmod,
    p ∈ P.V_mod_bad →
      Nat.Coprime (NumberFieldFinitePlace.residueCharacteristic p) l.value
  sourceQParameterOrder : ∀ w : NumberField.FinitePlace A.F,
    NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad → Nat
  sourceQParameterOrder_pos : ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      0 < sourceQParameterOrder w hw
  sourceQParameterOrder_primeToL : ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime (sourceQParameterOrder w hw) l.value

namespace BadPlaceReductionCards

variable {P : SourcePlaceSelection A}

/-- A split-multiplicative card determines the multiplicative and stable
cards, by the split inclusion and the stable union. -/
theorem ofSplitMultiplicative
    (splitReduction : ∀ w : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad →
        A.curve.HasSplitMultiplicativeReductionAt w) :
    BadPlaceReductionCards P where
  stableReduction := fun w hw =>
    A.curve.hasMultiplicativeReductionAt_imp_stable
      (A.curve.hasSplitMultiplicativeReductionAt_imp_multiplicative
        (splitReduction w hw))
  multiplicativeReduction := fun w hw =>
    A.curve.hasSplitMultiplicativeReductionAt_imp_multiplicative
      (splitReduction w hw)
  splitMultiplicativeReduction := splitReduction

theorem stable_spec (C : BadPlaceReductionCards P)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    A.curve.HasStableReductionAt w :=
  C.stableReduction w hw

theorem multiplicative_spec (C : BadPlaceReductionCards P)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    A.curve.HasMultiplicativeReductionAt w :=
  C.multiplicativeReduction w hw

theorem splitMultiplicative_spec (C : BadPlaceReductionCards P)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    A.curve.HasSplitMultiplicativeReductionAt w :=
  C.splitMultiplicativeReduction w hw

end BadPlaceReductionCards

/-- Clause (b) fibre form: reduction of the curve over the bad fibre. -/
def HasStableReductionOver (P : SourcePlaceSelection A) (b : Bad P) : Prop :=
  ∀ w : NumberField.FinitePlace A.F,
    NumberFieldFinitePlace.comap (k := A.Fmod) w = b.1 →
      A.curve.HasStableReductionAt w

def HasMultiplicativeReductionOver (P : SourcePlaceSelection A) (b : Bad P) :
    Prop :=
  ∀ w : NumberField.FinitePlace A.F,
    NumberFieldFinitePlace.comap (k := A.Fmod) w = b.1 →
      A.curve.HasMultiplicativeReductionAt w

def HasSplitMultiplicativeReductionOver (P : SourcePlaceSelection A)
    (b : Bad P) : Prop :=
  ∀ w : NumberField.FinitePlace A.F,
    NumberFieldFinitePlace.comap (k := A.Fmod) w = b.1 →
      A.curve.HasSplitMultiplicativeReductionAt w

theorem hasStableReductionOver_of_cards (P : SourcePlaceSelection A)
    (C : BadPlaceReductionCards P) (b : Bad P) :
    HasStableReductionOver P b :=
  fun w hw => C.stableReduction w (by rw [hw]; exact b.2)

theorem hasMultiplicativeReductionOver_of_cards
    (P : SourcePlaceSelection A) (C : BadPlaceReductionCards P) (b : Bad P) :
    HasMultiplicativeReductionOver P b :=
  fun w hw => C.multiplicativeReduction w (by rw [hw]; exact b.2)

theorem hasSplitMultiplicativeReductionOver_of_cards
    (P : SourcePlaceSelection A) (C : BadPlaceReductionCards P) (b : Bad P) :
    HasSplitMultiplicativeReductionOver P b :=
  fun w hw => C.splitMultiplicativeReduction w (by rw [hw]; exact b.2)

theorem hasMultiplicativeReductionOver_of_split
    (P : SourcePlaceSelection A) (b : Bad P)
    (h : HasSplitMultiplicativeReductionOver P b) :
    HasMultiplicativeReductionOver P b :=
  fun w hw =>
    A.curve.hasSplitMultiplicativeReductionAt_imp_multiplicative (h w hw)

theorem hasStableReductionOver_of_multiplicative
    (P : SourcePlaceSelection A) (b : Bad P)
    (h : HasMultiplicativeReductionOver P b) :
    HasStableReductionOver P b :=
  fun w hw => A.curve.hasMultiplicativeReductionAt_imp_stable (h w hw)

theorem hasStableReductionOver_of_split (P : SourcePlaceSelection A)
    (b : Bad P) (h : HasSplitMultiplicativeReductionOver P b) :
    HasStableReductionOver P b :=
  hasStableReductionOver_of_multiplicative P b
    (hasMultiplicativeReductionOver_of_split P b h)

/-- The D4 conditional assembly into the Theorem 3.11 source boundary. The
reduction content is exactly the three cards; the real parameter is the
completed-DVR proxy, and its identification with the Tate q-parameter is the
recorded boundary. -/
def toSourceReductionClause (P : SourcePlaceSelection A)
    [Fintype (Bad P)] (C : BadPlaceReductionCards P) :
    Theorem311Source.SourceReductionClause (Selected P) (Bad P) where
  partition := toSourcePlacePartition P
  stableReduction := HasStableReductionOver P
  stableReduction_proved := fun b => hasStableReductionOver_of_cards P C b
  multiplicativeReduction := HasMultiplicativeReductionOver P
  multiplicativeReduction_proved := fun b =>
    hasMultiplicativeReductionOver_of_cards P C b
  splitMultiplicativeReduction := HasSplitMultiplicativeReductionOver P
  splitMultiplicativeReduction_proved := fun b =>
    hasSplitMultiplicativeReductionOver_of_cards P C b
  reductionCompatibility := fun b =>
    hasMultiplicativeReductionOver_of_split P b
  qParameter := fun b => badPlaceQProxy P b
  qParameter_nonzero := fun b => badPlaceQProxy_ne_zero P b
  qParameter_contracting := fun b => badPlaceQProxy_norm_lt_one P b
  qParameter_reduction_compatibility := fun b _ => badPlaceQProxy_ne_one P b

theorem d3_d4_reduction_pass_bundle (P : SourcePlaceSelection A)
    [Fintype (Bad P)] (C : BadPlaceReductionCards P) :
    Function.Bijective (kindEquiv P) ∧
      (∀ w : Selected P,
        (∃ p : NumberField.FinitePlace A.Fmod, finiteToV P p = w) ∨
          (∃ s : NumberField.InfinitePlace A.Fmod, infiniteToV P s = w)) ∧
      (∀ (p : NumberField.FinitePlace A.Fmod)
        (s : NumberField.InfinitePlace A.Fmod),
          finiteToV P p ≠ infiniteToV P s) ∧
      (∀ p : NumberField.FinitePlace A.Fmod,
        NumberFieldPlace.comap (k := A.Fmod) (finiteToV P p).1 =
          NumberFieldPlace.finite p) ∧
      (∀ p : NumberField.FinitePlace A.Fmod,
        NumberFieldFinitePlace.relativeCompletionDegree (k := A.Fmod)
          (sectionFiniteLift P p) ≤ Module.finrank A.Fmod A.K) ∧
      (∀ p : NumberField.FinitePlace A.Fmod,
        NumberFieldFinitePlace.residueLocalDegree (sectionFiniteLift P p) ≤
          Module.finrank ℚ A.K) ∧
      (∀ p : NumberField.FinitePlace A.Fmod, p ∈ P.V_mod_bad →
        Odd (NumberFieldFinitePlace.residueCharacteristic p)) ∧
      (∀ b : Bad P, (toSourceReductionClause P C).stableReduction b) ∧
      (∀ b : Bad P, (toSourceReductionClause P C).qParameter b ≠ 0) ∧
      (∀ b : Bad P, ‖(toSourceReductionClause P C).qParameter b‖ < 1) ∧
      (∀ b : Bad P, (toSourceReductionClause P C).qParameter b ≠ 1) :=
  ⟨kindEquiv_bijective P,
    selected_kind_cover P,
    fun p s => finiteToV_ne_infiniteToV P p s,
    finiteToV_comap P,
    relativeCompletionDegree_sectionFiniteLift_le P,
    residueLocalDegree_sectionFiniteLift_le P,
    fun p hp => P.V_mod_bad_odd_residue_characteristic p hp,
    (toSourceReductionClause P C).stableReduction_proved,
    (toSourceReductionClause P C).qParameter_nonzero,
    (toSourceReductionClause P C).qParameter_contracting,
    fun b => (toSourceReductionClause P C).qParameter_reduction_compatibility b
      ((toSourceReductionClause P C).stableReduction_proved b)⟩

end PlacePartitionReduction

end InitialThetaSource

namespace Audit

def sourcePlacePartitionArithmeticConstruction : Obligation :=
  { id := "IUT-I.definition-3.1-D3-place-partition"
    source := "IUT I, Definition 3.1(a)(b)(e): the places V(F), V_non, V_arc, V_bad, V_good"
    status := VerificationStatus.conditional
    note :=
      "From InitialThetaArithmeticData and the source selection " ++
        "SourcePlaceSelection (bad moduli set, odd residue characteristic, " ++
        "nonemptiness), the finite/infinite index partition of V(F) is " ++
        "constructed: kindEquiv is a bijection, the finite and infinite images " ++
        "cover V(F) and are disjoint, restriction of a selected finite place is " ++
        "the moduli place, and fibre degrees satisfy e*f sum equals the relative " ++
        "degree with the local degree bounded by the absolute degree. The bad " ++
        "set remains a source input; no arbitrary-input existence of " ++
        "InitialThetaArithmeticData is asserted."
    dependsOn :=
      [ "IUT-I.definition-3.1-D2",
        "IUT-I.initial-theta-reduction-place-partition",
        "Foundations.NumberField.finite-place-completion-global-degree" ] }

def sourcePlacePartitionPrimeStripLabels : Obligation :=
  { id := "IUT-I.definition-3.1-D3-prime-strip-labels"
    source := "IUT I, Definition 3.1(b): residue characteristics of the bad moduli places"
    status := VerificationStatus.conditional
    note :=
      "The residue-characteristic labels of the bad places are proved: the " ++
        "label of a selected bad place equals the residue characteristic of its " ++
        "moduli place, the label is prime and odd, and it defines a rational " ++
        "prime place together with an index in every prime-strip interval " ++
        "containing the characteristic. The Frobenioid strip object itself is " ++
        "not constructed."
    dependsOn :=
      [ "IUT-I.definition-3.1-D3-place-partition",
        "Foundations.Arithmetic.prime-intervals" ] }

def sourceReductionCards : Obligation :=
  { id := "IUT-I.definition-3.1-D4-reduction-cards"
    source := "IUT I, Definition 3.1(b)(c): stable and multiplicative reduction, q-parameter orders"
    status := VerificationStatus.pending
    note :=
      "The named cards BadPlaceReductionCards (stable, multiplicative, split " ++
        "multiplicative reduction over the bad fibre of the curve field F) and " ++
        "BadPlaceQParameterCards (coprimality of the bad residue " ++
        "characteristics with l, and the prime-to-l orders of the source " ++
        "q-parameters) are frozen. No proof that the curve has multiplicative " ++
        "reduction, and no Tate-uniformization identification of the " ++
        "completed-DVR q-candidate with the source q-parameter, is available."
    dependsOn :=
      [ "IUT-I.definition-3.1-D3-place-partition",
        "Foundations.Geometry.elliptic-local-reduction",
        "Foundations.NumberField.local-q-parameter-valuation" ] }

def sourceReductionClauseAssembly : Obligation :=
  { id := "IUT-I.definition-3.1-D4-clause-assembly"
    source := "IUT I, Definition 3.1(b): the reduction clause of the source contract"
    status := VerificationStatus.conditional
    note :=
      "Given the frozen reduction cards, the source reduction clause is " ++
        "assembled: split multiplicative implies multiplicative implies stable, " ++
        "and the real parameter derived from the completed discrete valuation " ++
        "ring candidate is nonzero, contracting, and not one. The parameter is " ++
        "valuation-theoretic; the identification with the Tate q-parameter of " ++
        "the curve remains open."
    dependsOn :=
      [ "IUT-I.definition-3.1-D4-reduction-cards",
        "IUT-I.definition-3.1-D3-prime-strip-labels" ] }

end Audit

end

end LeanFormal.IUT
