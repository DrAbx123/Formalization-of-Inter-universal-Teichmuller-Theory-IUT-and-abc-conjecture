import LeanFormal.IUT.IUTII.Frobenioid.Example36FrobenioidTransport
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import LeanFormal.IUT.ABCBridge.Geometry.LegendreQuadraticParameterFields
import Mathlib.Tactic

/-!
# A concrete/generic instance of `PlaceLocalizationTransport` from a number-field extension

This file instantiates the abstract place-localization transport datum of
`Example36FrobenioidTransport.lean` with an actual finite extension of number
fields: the finite-place restriction is ideal contraction (`comap`), the
ramification index is the genuine `ramificationIdx'` of the upstairs and
downstairs maximal ideals, and the local extension laws are proved from the
standard ramification formula for valuations and from the identity of
archimedean absolute values along the restricted embedding.

Boundary: the effective-cone fields are proved for the actual number-field
value data (the cones are the nonnegative integer and nonnegative real cones).
The concrete quadratic example is `Q(sqrt 2) / Q`; its ramification index
above `(2)` is the genuine arithmetic one, but the numerical computation
`e = 2` is not carried out here and is recorded as an explicit missing
computation at the end of the file.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField
open IsDedekindDomain NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]
variable {F' : Type u} [Field F'] [NumberField F'] [Algebra F F'] [FiniteDimensional F F']

/-- The finite place of `F` below a finite place of `F'`: contraction of the
maximal ideal along the rings of integers. -/
def upperPlaceRestriction (w : HeightOneSpectrum (𝓞 F')) : HeightOneSpectrum (𝓞 F) :=
  (NumberFieldFinitePlace.comap (k := F) (NumberField.FinitePlace.mk w)).maximalIdeal

/-- The genuine ramification index of a finite place of the extension over its
contraction: the ideal ramification index of the upstairs maximal ideal over the
downstairs maximal ideal. -/
def ramificationIndexAtUpperPlace (w : HeightOneSpectrum (𝓞 F')) : ℕ :=
  (NumberFieldFinitePlace.comap (k := F) (NumberField.FinitePlace.mk w)).maximalIdeal.asIdeal
    |>.ramificationIdx' (NumberField.FinitePlace.mk w).maximalIdeal.asIdeal

/-- The archimedean place of `F` below an archimedean place of `F'`: restriction
of the absolute value along the embedding of `F` into `F'`. -/
def upperInfinitePlaceRestriction (w : NumberField.InfinitePlace F') :
    NumberField.InfinitePlace F :=
  w.comap (algebraMap F F')

/-- Only finitely many finite places of `F'` restrict to a given finite set of
places of `F`: the fiber over a place is the finite set of primes over its
maximal ideal. -/
theorem upperPlaceRestriction_finite (s : Finset (HeightOneSpectrum (𝓞 F))) :
    {w : HeightOneSpectrum (𝓞 F') | upperPlaceRestriction w ∈ s}.Finite := by
  classical
  have hfib : ∀ v : HeightOneSpectrum (𝓞 F),
      {w : HeightOneSpectrum (𝓞 F') | upperPlaceRestriction w = v}.Finite := by
    intro v
    have hfin : (v.asIdeal.primesOver (𝓞 F')).Finite :=
      IsDedekindDomain.primesOver_finite (A := 𝓞 F) (B := 𝓞 F') v.asIdeal
    haveI : Finite (v.asIdeal.primesOver (𝓞 F')) :=
      Set.finite_coe_iff.mpr hfin
    let f : {w : HeightOneSpectrum (𝓞 F') | upperPlaceRestriction w = v} →
        (v.asIdeal.primesOver (𝓞 F')) := fun w =>
      ⟨w.1.asIdeal, w.1.isPrime, by
        have hv : v.asIdeal = (upperPlaceRestriction (F := F) w.1).asIdeal := by
          rw [w.2]
        have hc : (upperPlaceRestriction (F := F) w.1).asIdeal =
            w.1.asIdeal.comap
              (algebraMap (𝓞 F) (𝓞 F')) := by
          have hraw := NumberFieldFinitePlace.comap_maximalIdeal
            (k := F) (K := F')
            (place := NumberField.FinitePlace.mk w.1)
          rw [NumberField.FinitePlace.maximalIdeal_mk] at hraw
          exact hraw
        exact (Ideal.liesOver_iff _ _).mpr (hv.trans hc)⟩
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact HeightOneSpectrum.ext (congrArg Subtype.val hab)
    haveI : Finite {w : HeightOneSpectrum (𝓞 F') | upperPlaceRestriction w = v} :=
      Finite.of_injective f hinj
    exact Set.finite_coe_iff.mp inferInstance
  have hset : {w : HeightOneSpectrum (𝓞 F') | upperPlaceRestriction w ∈ s} =
      ⋃ v ∈ (s : Set (HeightOneSpectrum (𝓞 F))),
        {w : HeightOneSpectrum (𝓞 F') | upperPlaceRestriction w = v} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hw
      exact ⟨upperPlaceRestriction w, hw, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  rw [hset]
  exact Set.Finite.biUnion s.finite_toSet (fun v _ => hfib v)

/-- The ramification index at an upstairs place is positive. -/
theorem ramificationIndexAtUpperPlace_pos (w : HeightOneSpectrum (𝓞 F')) :
    0 < ramificationIndexAtUpperPlace (F := F) (F' := F') w :=
  Nat.pos_of_ne_zero (by
    exact NumberFieldFinitePlace.ramificationIdx_ne_zero (k := F)
      (place := NumberField.FinitePlace.mk w))

/-- The generic place-localization transport datum for a finite extension of
number fields `F -> F'`: restriction of finite places by `comap`, genuine
ramification indices, restriction of archimedean places by `comap`, and the
local extension laws proved from the arithmetic of the extension. -/
def PlaceLocalizationTransport.ofNumberFieldExtension :
    PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F')) where
  fieldMap := algebraMap F F'
  finitePlaceRestriction := upperPlaceRestriction (F := F)
  infinitePlaceRestriction := upperInfinitePlaceRestriction (F := F)
  finitePlaceRestriction_finite := upperPlaceRestriction_finite (F := F)
  ramificationIndex := ramificationIndexAtUpperPlace (F := F)
  ramificationIndex_pos := ramificationIndexAtUpperPlace_pos (F := F)
  finiteDelta_transport := by
    intro f w
    rw [numberFieldGlobalPlaceData_finiteDelta, numberFieldGlobalPlaceData_finiteDelta]
    unfold finitePlaceValueExponent
    have hval := NumberFieldFinitePlace.valuation_algebraMap (k := F) (K := F')
      (place := NumberField.FinitePlace.mk w) (x := (f : F))
    rw [NumberField.FinitePlace.maximalIdeal_mk] at hval
    have hlog : WithZero.log (w.valuation F' (algebraMap F F' (f : F))) =
        (ramificationIndexAtUpperPlace (F := F) (F' := F') w : ℤ) *
          WithZero.log ((upperPlaceRestriction (F := F) w).valuation F (f : F)) := by
      rw [← hval, WithZero.log_pow, nsmul_eq_mul]
      unfold ramificationIndexAtUpperPlace upperPlaceRestriction
      rw [NumberField.FinitePlace.maximalIdeal_mk]
    rw [show ((unitsMapOfRingHom (algebraMap F F') f : F'ˣ) : F') =
        algebraMap F F' (f : F) from unitsMapOfRingHom_apply_coe _ f]
    rw [hlog, mul_neg]
  infiniteDelta_transport := by
    intro f w
    rw [numberFieldGlobalPlaceData_infiniteDelta, numberFieldGlobalPlaceData_infiniteDelta]
    congr 1
  finiteCone_transport := by
    intro w a ha
    change (ramificationIndexAtUpperPlace (F := F) (F' := F') w • a) ∈ integerNonnegCone
    change a ∈ integerNonnegCone at ha
    rw [mem_integerNonnegCone] at ha ⊢
    rw [nsmul_eq_mul]
    exact mul_nonneg (Int.natCast_nonneg _) ha
  infiniteCone_transport := by
    intro w a ha
    change a ∈ realNonnegCone at ha ⊢
    exact ha

/-- The finite-place local extension law for global units, restated as a named
theorem of the generic instance. -/
theorem ofNumberFieldExtension_finiteDelta (f : Fˣ) (w : HeightOneSpectrum (𝓞 F')) :
    (numberFieldGlobalPlaceData (F := F')).finiteDelta
        (unitsMapOfRingHom (algebraMap F F') f) w =
      (ramificationIndexAtUpperPlace (F := F) (F' := F') w : ℤ) *
        (numberFieldGlobalPlaceData (F := F)).finiteDelta f
          (upperPlaceRestriction (F := F) w) :=
  (PlaceLocalizationTransport.ofNumberFieldExtension (F := F) (F' := F')).finiteDelta_transport f w

/-- The archimedean local extension law for the generic instance. -/
theorem ofNumberFieldExtension_infiniteDelta (f : Fˣ)
    (w : NumberField.InfinitePlace F') :
    (numberFieldGlobalPlaceData (F := F')).infiniteDelta
        (unitsMapOfRingHom (algebraMap F F') f) w =
      (numberFieldGlobalPlaceData (F := F)).infiniteDelta f
        (upperInfinitePlaceRestriction (F := F) w) :=
  (PlaceLocalizationTransport.ofNumberFieldExtension (F := F) (F' := F')).infiniteDelta_transport f w

/-- Completion-bridge compatibility: on the lower completion the genuine
extension map satisfies the ramification formula with the recorded ramification
index of the instance.  This is the local-field form of the finite-place
transport law. -/
theorem ofNumberFieldExtension_completion_valuation
    (w : HeightOneSpectrum (𝓞 F'))
    (x : (upperPlaceRestriction (F := F) w).adicCompletion F) :
    Valued.v x ^ (ramificationIndexAtUpperPlace (F := F) (F' := F') w) =
      Valued.v (NumberFieldFinitePlace.completionMap (k := F)
        (place := NumberField.FinitePlace.mk w) x) := by
  exact NumberFieldFinitePlace.valuation_completionMap (k := F) (K := F')
    (place := NumberField.FinitePlace.mk w) x

/-! ## Concrete quadratic instance: `Q(sqrt 2) / Q` -/

open LeanFormal.IUT.LegendreQuadraticParameterFields

/-- The concrete transport instance for the quadratic number field obtained by
adjoining a square root of `2` to `Q`.  The finite-place restriction is the
genuine ideal contraction and the ramification index is the genuine arithmetic
ramification index of each upstairs place. -/
def quadraticSquareRootTwoTransport :
    PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := ℚ))
      (numberFieldGlobalPlaceData (F := squareRootField ℚ 2)) :=
  PlaceLocalizationTransport.ofNumberFieldExtension (F := ℚ) (F' := squareRootField ℚ (2 : ℚ))

/-- The ramification indices of the concrete quadratic transport are the actual
ramification indices of the extension, by construction. -/
@[simp]
theorem quadraticSquareRootTwoTransport_ramificationIndex
    (w : HeightOneSpectrum (𝓞 (squareRootField ℚ (2 : ℚ)))) :
    quadraticSquareRootTwoTransport.ramificationIndex w =
      ramificationIndexAtUpperPlace (F := ℚ) (F' := squareRootField ℚ (2 : ℚ)) w :=
  rfl

/-- The exact missing computation for the concrete ramified example: the
arithmetic ramification index above `(2)` in `Q(sqrt 2) / Q` equals two.
The transport datum does record the genuine (nontrivial) ramification indices;
only the numerical evaluation `e = 2` at the place above `2` is not carried out
in this file. -/
def quadraticRamificationMissingComputation : Prop :=
  ∃ w : HeightOneSpectrum (𝓞 (squareRootField ℚ (2 : ℚ))),
    ramificationIndexAtUpperPlace (F := ℚ) (F' := squareRootField ℚ (2 : ℚ)) w = 2

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
end
