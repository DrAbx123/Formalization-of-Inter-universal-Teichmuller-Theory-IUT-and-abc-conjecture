import LeanFormal.IUT.ABCBridge.Geometry.AdicCompletionValuationUniqueness
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegreeGlobal
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs

open scoped Valued

namespace LeanFormal.IUT

universe u v

namespace NumberFieldFinitePlace

noncomputable section

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-! ## The finiteness input as an elementwise integrality statement

The remaining unproved input of the local fundamental identity
`Module.finrank k_v K_w = e * f` is the finiteness of the completed upper valuation
ring `𝒪_w` over the completed lower valuation ring `𝒪_v`. This section reduces that
input to the statement that every element of `𝒪_w` is integral over `𝒪_v`;
equivalently, that `𝒪_w` is the integral closure of `𝒪_v` in `K_w`, which is the
uniqueness of the extension of the complete valuation. The predecessor file proves
the unconditional inclusion `integralClosure 𝒪_v K_w ≤ 𝒪_w` and derives finiteness
from `IsIntegralClosure`; here the converse implication is added, by the general fact
that a finite algebra is integral.

The companion local-input agreement `localDataAgreesWithPlaceData` is discharged
unconditionally by the imported module `FinitePlaceCompletionLocalInputs`
(`localDataAgreesWithPlaceData_adicCompletion`); the target identity at the end of
this file is therefore conditional on the finiteness input alone. -/

/-- **Gap-A reduction, assembly step.** If every element of the upper completed
valuation ring is integral over the lower completed valuation ring, then `𝒪_w` is the
integral closure of `𝒪_v` in `K_w`: the forward inclusion `integralClosure 𝒪_v K_w ≤ 𝒪_w`
is the unconditional theorem of the predecessor file, and the converse is the
hypothesis. -/
theorem isIntegralClosure_adicCompletionIntegers_of_forall_isIntegral
    (place : NumberField.FinitePlace K)
    (hint : ∀ y : place.maximalIdeal.adicCompletion K,
      y ∈ (place.maximalIdeal.adicCompletionIntegers K :
        Set (place.maximalIdeal.adicCompletion K)) →
      IsIntegral ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) y) :
    IsIntegralClosure (place.maximalIdeal.adicCompletionIntegers K)
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletion K) where
  algebraMap_injective := fun x y hxy => Subtype.ext hxy
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ (integralClosure
          ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
          (place.maximalIdeal.adicCompletion K) :
            Set (place.maximalIdeal.adicCompletion K)) :=
        (mem_integralClosure_iff
          ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
          (place.maximalIdeal.adicCompletion K)).mpr hx
      exact ⟨⟨x, integralClosure_le_adicCompletionIntegers (k := k) place hx'⟩, rfl⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact hint y y.2

/- Separability of the completion extension, `Algebra.IsSeparable k_v K_w`, is
provided unconditionally by the imported module `FinitePlaceCompletionLocalInputs`
as its declaration `isSeparable_adicCompletion` (same statement: characteristic zero
plus finiteness of the completion algebra, hence integrality, hence separability).
The local copy carried the same fully qualified name and was removed upon importing
the module, to keep one canonical declaration; all uses below resolve to it. -/

/-- **Gap-A reduction, finiteness step.** Under the elementwise integrality input, the
upper completed valuation ring is a finite module over the lower one, by
`IsIntegralClosure.finite` applied to the assembled integral-closure statement. -/
theorem moduleFinite_adicCompletionIntegers_of_forall_isIntegral
    (place : NumberField.FinitePlace K)
    (hint : ∀ y : place.maximalIdeal.adicCompletion K,
      y ∈ (place.maximalIdeal.adicCompletionIntegers K :
        Set (place.maximalIdeal.adicCompletion K)) →
      IsIntegral ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) y) :
    Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K) :=
  moduleFinite_adicCompletionIntegers_of_isIntegralClosure (k := k) place
    (isSeparable_adicCompletion (k := k) place)
    (isIntegralClosure_adicCompletionIntegers_of_forall_isIntegral (k := k) place hint)

/-- **Gap-A reduction, equivalence form.** The finiteness of `𝒪_w` over `𝒪_v` holds
exactly when every element of `𝒪_w` is integral over `𝒪_v`. The forward implication
uses that a finite algebra is integral together with the unconditional inclusion
`integralClosure 𝒪_v K_w ≤ 𝒪_w`; the converse is the finiteness step above. -/
theorem moduleFinite_iff_forall_isIntegral_adicCompletionIntegers
    (place : NumberField.FinitePlace K) :
    Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
        (place.maximalIdeal.adicCompletionIntegers K) ↔
      ∀ y : place.maximalIdeal.adicCompletion K,
        y ∈ (place.maximalIdeal.adicCompletionIntegers K :
          Set (place.maximalIdeal.adicCompletion K)) →
        IsIntegral ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) y := by
  constructor
  · intro hfinite y hy
    haveI := hfinite
    have h := IsIntegral.of_finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (⟨y, hy⟩ : place.maximalIdeal.adicCompletionIntegers K)
    exact h.map (IsScalarTower.toAlgHom
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K)
      (place.maximalIdeal.adicCompletion K))
  · exact moduleFinite_adicCompletionIntegers_of_forall_isIntegral (k := k) place

/-- **Gap-A reduction, integral-closure form.** The elementwise integrality input is
exactly the statement that `𝒪_w` is the integral closure of `𝒪_v` in `K_w`. This is
the canonical form of the uniqueness of the extension of the complete valuation, and
it is the precise statement which Mathlib 4.32.2 does not supply for adic
completions. -/
theorem forall_isIntegral_iff_isIntegralClosure_adicCompletionIntegers
    (place : NumberField.FinitePlace K) :
    (∀ y : place.maximalIdeal.adicCompletion K,
        y ∈ (place.maximalIdeal.adicCompletionIntegers K :
          Set (place.maximalIdeal.adicCompletion K)) →
        IsIntegral ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) y) ↔
      IsIntegralClosure (place.maximalIdeal.adicCompletionIntegers K)
        ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
        (place.maximalIdeal.adicCompletion K) := by
  constructor
  · exact isIntegralClosure_adicCompletionIntegers_of_forall_isIntegral (k := k) place
  · intro hclosure y hy
    exact hclosure.isIntegral_iff.mpr ⟨⟨y, hy⟩, rfl⟩

/-- **Gap-A reduction, integral-closure form of finiteness.** The finiteness of `𝒪_w`
over `𝒪_v` holds exactly when `𝒪_w` is the integral closure of `𝒪_v` in `K_w`. -/
theorem moduleFinite_iff_isIntegralClosure_adicCompletionIntegers
    (place : NumberField.FinitePlace K) :
    Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
        (place.maximalIdeal.adicCompletionIntegers K) ↔
      IsIntegralClosure (place.maximalIdeal.adicCompletionIntegers K)
        ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
        (place.maximalIdeal.adicCompletion K) :=
  (moduleFinite_iff_forall_isIntegral_adicCompletionIntegers (k := k) place).trans
    (forall_isIntegral_iff_isIntegralClosure_adicCompletionIntegers (k := k) place)

/-! ## The reduction form of `finrank k_v K_w = e * f` -/

/-- **The target identity from the finiteness input alone.** Given the finiteness of
`𝒪_w` over `𝒪_v`, the degree of the completion extension equals the relative degree
`e * f`. The agreement of the local ramification index and local residue degree with
the library data of the place extension is discharged unconditionally by the imported
theorem `localDataAgreesWithPlaceData_adicCompletion`, so the finiteness of `𝒪_w`
over `𝒪_v` is the only remaining hypothesis. -/
theorem finrank_adicCompletion_eq_ramificationIndex_mul_residueDegree
    (place : NumberField.FinitePlace K)
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K)) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      relativeRamificationIndex (k := k) place *
        relativeResidueDegree (k := k) place := by
  rw [finrank_adicCompletion_eq_relativeCompletionDegree (k := k) place hfinite
      (localDataAgreesWithPlaceData_adicCompletion (k := k) place),
    relativeCompletionDegree]

/-- **The target identity from the reduced input.** With the finiteness input reduced to
the elementwise integrality statement, the fundamental identity holds; the local-data
agreement is discharged unconditionally by the imported module. -/
theorem finrank_adicCompletion_eq_ramificationIndex_mul_residueDegree_of_forall_isIntegral
    (place : NumberField.FinitePlace K)
    (hint : ∀ y : place.maximalIdeal.adicCompletion K,
      y ∈ (place.maximalIdeal.adicCompletionIntegers K :
        Set (place.maximalIdeal.adicCompletion K)) →
      IsIntegral ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) y) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      relativeRamificationIndex (k := k) place *
        relativeResidueDegree (k := k) place :=
  finrank_adicCompletion_eq_ramificationIndex_mul_residueDegree (k := k) place
    (moduleFinite_adicCompletionIntegers_of_forall_isIntegral (k := k) place hint)

/-- **The target identity from the integral-closure input.** With the finiteness input
consumed in the integral-closure form, the fundamental identity holds; the local-data
agreement is discharged unconditionally by the imported module, and separability of
the completed extension is supplied by the imported module as well. -/
theorem finrank_adicCompletion_eq_ramificationIndex_mul_residueDegree_of_isIntegralClosure
    (place : NumberField.FinitePlace K)
    (hclosure : IsIntegralClosure (place.maximalIdeal.adicCompletionIntegers K)
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletion K)) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      relativeRamificationIndex (k := k) place *
        relativeResidueDegree (k := k) place :=
  finrank_adicCompletion_eq_ramificationIndex_mul_residueDegree (k := k) place
    (moduleFinite_adicCompletionIntegers_of_isIntegralClosure (k := k) place
      (isSeparable_adicCompletion (k := k) place) hclosure)

/-! ## Gap-A discharged: the unconditional local fundamental identity -/

/-- **Gap-A, unconditional.** The upper completed valuation ring is the integral closure
of the lower one in the completed upper field. Card (A) of the finrank reduction is
proved unconditionally in the companion module `AdicCompletionValuationUniqueness`
(`moduleFinite_adicCompletionIntegers`); this is its integral-closure form through the
equivalence `moduleFinite_iff_isIntegralClosure_adicCompletionIntegers`. -/
theorem isIntegralClosure_adicCompletionIntegers (place : NumberField.FinitePlace K) :
    IsIntegralClosure (place.maximalIdeal.adicCompletionIntegers K)
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletion K) :=
  (moduleFinite_iff_isIntegralClosure_adicCompletionIntegers (k := k) place).mp
    (moduleFinite_adicCompletionIntegers (k := k) place)

/-- **The unconditional local fundamental identity** `finrank k_v K_w = e * f`. Both
previously conditional inputs are discharged: the local-data agreement by the imported
module `FinitePlaceCompletionLocalInputs`, and the finiteness of `𝒪_w` over `𝒪_v` by the
imported module `AdicCompletionValuationUniqueness`. -/
theorem finrank_adicCompletion_eq_ramificationIndex_mul_residueDegree_unconditional
    (place : NumberField.FinitePlace K) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      relativeRamificationIndex (k := k) place *
        relativeResidueDegree (k := k) place :=
  finrank_adicCompletion_eq_ramificationIndex_mul_residueDegree (k := k) place
    (moduleFinite_adicCompletionIntegers (k := k) place)

/-! ## Wiring the unconditional inputs into the retained conditional consumers -/

/-- **Consumer `finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree`
discharged.** The `e_loc * f_loc` form of the local fundamental identity, with the
finiteness input (card A) supplied unconditionally by `moduleFinite_adicCompletionIntegers`. -/
theorem finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree_unconditional
    (place : NumberField.FinitePlace K) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      localRamificationIndex (k := k) place * localInertiaDegree (k := k) place :=
  finrank_adicCompletion_eq_localRamificationIndex_mul_localInertiaDegree (k := k) place
    (moduleFinite_adicCompletionIntegers (k := k) place)

/-- **Consumer `finrank_adicCompletion_eq_relativeCompletionDegree` discharged.** The
`finrank = relativeCompletionDegree` form with both named inputs supplied unconditionally
(card A by `moduleFinite_adicCompletionIntegers`, card B by
`localDataAgreesWithPlaceData_adicCompletion`). This is the exact hypothesis shape of the
`_of_finrank_eq_relativeCompletionDegree` transports. -/
theorem finrank_adicCompletion_eq_relativeCompletionDegree_unconditional
    (place : NumberField.FinitePlace K) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      relativeCompletionDegree (k := k) place :=
  finrank_adicCompletion_eq_relativeCompletionDegree (k := k) place
    (moduleFinite_adicCompletionIntegers (k := k) place)
    (localDataAgreesWithPlaceData_adicCompletion (k := k) place)

/-- **Consumer `sum_finrank_adicCompletion_eq_fieldDegree` discharged.** The global
degree sum formula `∑_{w | v} [K_w : k_v] = [K : k]`, unconditional: both fibre-wise
named inputs are discharged by the two theorems above. This closes the level-1 gap
recorded as not reached in `FinitePlaceCompletionDegreeGlobal.lean`. -/
theorem sum_finrank_adicCompletion_eq_fieldDegree_unconditional
    (lowerPlace : NumberField.FinitePlace k) :
    (∑ upperPlace : PlacesAbove (K := K) lowerPlace,
      Module.finrank ((comap (k := k) upperPlace.val).maximalIdeal.adicCompletion k)
        (upperPlace.val.maximalIdeal.adicCompletion K)) = Module.finrank k K :=
  sum_finrank_adicCompletion_eq_fieldDegree (K := K) lowerPlace
    (fun upperPlace => moduleFinite_adicCompletionIntegers (k := k) upperPlace.val)
    (fun upperPlace => localDataAgreesWithPlaceData_adicCompletion (k := k) upperPlace.val)

/-! ## Hypothesis-free restatements of the transports at the actual local degree

The module `FinitePlaceCompletionNormTransport` states its norm transports with the
relative degree `e * f` and cannot restate them at the actual local degree
`Module.finrank k_v K_w`: the unconditional identity
`finrank_adicCompletion_eq_relativeCompletionDegree_unconditional` of this file is
downstream of that module. The six restatements below carry the same names as the
conditional bridges that previously stood in that module; each eliminates the
hypothesis `hfinrank` by the proved identity, so the transports are available at the
actual local degree without conditional input. The `[Algebra]` binder of the
conditional bridges is dropped: with the hypothesis eliminated the finrank is read
in the canonical completion algebra structure in which the identity is proved. -/

/-- Unconditional norm transport at the actual local degree: the canonical
completion norm of the image of a nonzero element is the lower canonical norm
raised to `Module.finrank k_v K_w`, by
`finrank_adicCompletion_eq_relativeCompletionDegree_unconditional`. -/
theorem norm_completionMap_pow_of_finrank_eq_relativeCompletionDegree
    (place : NumberField.FinitePlace K)
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    ‖completionMap (k := k) place x‖ =
      ‖x‖ ^ Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) := by
  rw [finrank_adicCompletion_eq_relativeCompletionDegree_unconditional (k := k) place]
  exact norm_completionMap_pow (k := k) place x hx

/-- Unconditional norm transport on elements of the base number field at the
actual local degree. -/
theorem norm_algebraMap_pow_of_finrank_eq_relativeCompletionDegree
    (place : NumberField.FinitePlace K)
    (a : k) (ha : a ≠ 0) :
    ‖(algebraMap k K a : place.maximalIdeal.adicCompletion K)‖ =
      ‖(a : (comap (k := k) place).maximalIdeal.adicCompletion k)‖ ^
        Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
          (place.maximalIdeal.adicCompletion K) := by
  rw [finrank_adicCompletion_eq_relativeCompletionDegree_unconditional (k := k) place]
  exact norm_algebraMap_pow (k := k) place a ha

/-- Unconditional logarithmic norm transport at the actual local degree. -/
theorem logNorm_completionMap_eq_mul_of_finrank_eq_relativeCompletionDegree
    (place : NumberField.FinitePlace K)
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    Real.log ‖completionMap (k := k) place x‖ =
      (Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) : ℝ) * Real.log ‖x‖ := by
  rw [finrank_adicCompletion_eq_relativeCompletionDegree_unconditional (k := k) place]
  exact logNorm_completionMap_eq_mul (k := k) place x hx

/-- Unconditional signed-magnitude transport at the actual local degree, in the
sign convention `-log‖-‖` of the q-pilot normalization chain. -/
theorem logMagnitude_completionMap_eq_mul_of_finrank_eq_relativeCompletionDegree
    (place : NumberField.FinitePlace K)
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    -Real.log ‖completionMap (k := k) place x‖ =
      (Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) : ℝ) * (-Real.log ‖x‖) := by
  rw [finrank_adicCompletion_eq_relativeCompletionDegree_unconditional (k := k) place]
  exact logMagnitude_completionMap_eq_mul (k := k) place x hx

/-- Unconditional logarithmic norm transport on elements of the base number
field at the actual local degree. -/
theorem logNorm_algebraMap_eq_mul_of_finrank_eq_relativeCompletionDegree
    (place : NumberField.FinitePlace K)
    (a : k) (ha : a ≠ 0) :
    Real.log ‖(algebraMap k K a : place.maximalIdeal.adicCompletion K)‖ =
      (Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) : ℝ) *
        Real.log ‖(a : (comap (k := k) place).maximalIdeal.adicCompletion k)‖ := by
  rw [finrank_adicCompletion_eq_relativeCompletionDegree_unconditional (k := k) place]
  exact logNorm_algebraMap_eq_mul (k := k) place a ha

/-- Unconditional absolute-degree-normalized transport at the actual local
degree: the normalization fraction `e * f / [K : k]` of the relative degree is
realized by `Module.finrank k_v K_w / [K : k]`, via
`finrank_adicCompletion_eq_relativeCompletionDegree_unconditional`. -/
theorem absoluteDegreeNormalizedLogNorm_completionMap_of_finrank_eq_relativeCompletionDegree
    (place : NumberField.FinitePlace K)
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    Real.log ‖completionMap (k := k) place x‖ / (Module.finrank ℚ K : ℝ) =
      ((Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
          (place.maximalIdeal.adicCompletion K) : ℝ) / (Module.finrank k K : ℝ)) *
        (Real.log ‖x‖ / (Module.finrank ℚ k : ℝ)) := by
  rw [finrank_adicCompletion_eq_relativeCompletionDegree_unconditional (k := k) place]
  exact absoluteDegreeNormalizedLogNorm_completionMap (k := k) place x hx
end

end NumberFieldFinitePlace

end LeanFormal.IUT
