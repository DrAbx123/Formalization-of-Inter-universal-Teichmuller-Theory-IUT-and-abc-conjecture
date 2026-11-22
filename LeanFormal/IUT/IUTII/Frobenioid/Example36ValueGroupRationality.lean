import LeanFormal.IUT.IUTII.Frobenioid.Example36ValueMapKernels
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripFrobenioidValueGroupRationality

set_option linter.unusedSectionVars false

/-!
# Value-group range and rationality statements for the actual place data

Boundary (2), value-group rationality/range fragment.  Task-17 (the actual
`V_K`/`rho_v` value maps of III Example 3.6) left three range statements as
named hypotheses: `FiniteValueMapRationalImage`, `InfiniteValueMapRationalImage`,
`PlaceValueMapRationalImage`, together with the degree-image form
`FiniteDegreeImageHypothesis`.  This module determines which of them the actual
number-field place data supports, proves the correct range theorems, and states
the precisely remaining source statement.  No range statement is assumed or
faked.

## What is proved

1. **The actual finite-place value coordinate of the global units is onto
   `Z`.**  A uniformizer of the discrete valuation ring `O_v` (Mathlib
   `HeightOneSpectrum.valuation_exists_uniformizer`) gives a global unit of
   exponent `1`; its integer powers are global units of every exponent.  Hence
   `finitePlaceValueExponent v : F^x -> Z` is surjective, the range of the
   actual finite value map is exactly the integer line
   `Set.range (fun k : Z => (k : R))`, and the composite
   `F^x -> (K_v)^x -> Gamma_v = Z` is onto the value group.
2. **The realified image is exactly the lattice `Z * log q_v`**, where
   `q_v = #(O_F / v)` is the actual residue-field cardinality
   (`finitePlaceResidueCardinality` of `Example36PrimeStripBridge`): the
   scaled value map `scale * finiteValueMap` has range `scale * Z`, and at
   `scale = log q_v` this is the degree image `Z * log q_v`.  The
   Frobenioid-value-kernel realification `-nu * log q_v` has range
   `Z * (-log q_v)`.
3. **The actual completion value map is onto `Z` with kernel `O_v^x`.**
   `completionValuationExponent v : (K_v)^x -> Z` is surjective and its zero
   locus is exactly the group of integral units `O_v^x`; the realified map
   has range the integer line, and its scaled version has range `scale * Z`.
4. **The actual archimedean log image** is the exact image
   `-log '' (archimedean absolute value image of F^x)`; it contains
   `-log 2` and all `+- n log 2` (via the global unit `2` and its inverse),
   so it is unbounded on the side `+n log 2`.  The archimedean value-GROUP
   realification is all of `R` (a value-group statement of
   `Example36PrimeStripBridge`), and hence cannot have rational image.
5. **Which named hypotheses hold / fail for the actual data.**
   `FiniteValueMapRationalImage`, `FiniteDegreeImageHypothesis` (any nonzero
   scale) and `PlaceValueMapRationalImage` at a finite place are REFUTED: the
   actual ranges are integer lattices, not the rational line; in particular the
   degree image is the lattice `Z * log q_v`, not `Q * log q_v`.
   `InfiniteValueMapRationalImage` and `PlaceValueMapRationalImage` at an
   archimedean place are NOT claimed: the exact archimedean image is stated in
   item 4, but no rationality statement about it is proved or refuted here.

## The exact remaining global source statement

The rational value group `Q` (and the degree image `Q * log p`) is a
statement about the *algebraically closed* local field: the tree proves it for
`(Qbar_p)^x` in
`PrimeStripFrobenioidValueGroupRationality.padicAlgCl_unit_logVal_range_eq_rat`
(restated as a consumer below; `provedKernel`, different carrier).  The actual
number-field data of Example 3.6 is the *discrete* completion `K_v` and the
global units `F^x`, whose value range is `Z` (this module).  The transport of
the rational `(Qbar_p)^x` value group to `F^x`/`K_v^x` is precisely the
missing source vertical carrier (the `V_K`/`rho_v` transport and log-Kummer /
log-shell carrier recorded in boundary (2), task-27); it is NOT constructed and
NOT claimed here.  Likewise `v((Q_p)^x) = Q` for the global unit group is not
claimed: the global unit range at a finite place is `Z`, and no map from
`(Qbar_p)^x` into `F^x` is available.

## Boundary

No fake range statement: every range equality below is proved for the actual
data.  Local unit group and global units are distinguished.  No theta-pilot,
q-pilot, Tate or Hodge-theater claim is made.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. The actual finite-place value coordinate of the global units is onto `Z` -/

/-- A global unit of `v`-adic exponent one: a uniformizer of the discrete
valuation ring at `v`, viewed as a unit of the fraction field. -/
noncomputable def finiteUniformizerUnit (v : HeightOneSpectrum (𝓞 F)) : Fˣ :=
  Units.mk0 (Classical.choose (HeightOneSpectrum.valuation_exists_uniformizer F v)) (by
    intro hzero
    have hspec := Classical.choose_spec (HeightOneSpectrum.valuation_exists_uniformizer F v)
    rw [hzero, map_zero] at hspec
    exact WithZero.exp_ne_zero hspec.symm)

/-- The uniformizer unit is the chosen uniformizer. -/
theorem finiteUniformizerUnit_coe (v : HeightOneSpectrum (𝓞 F)) :
    (finiteUniformizerUnit v : F) =
      Classical.choose (HeightOneSpectrum.valuation_exists_uniformizer F v) :=
  rfl

/-- The uniformizer unit has exponent one. -/
theorem finiteUniformizerUnit_exponent (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceValueExponent v (finiteUniformizerUnit v) = 1 := by
  unfold finitePlaceValueExponent
  rw [finiteUniformizerUnit_coe,
    Classical.choose_spec (HeightOneSpectrum.valuation_exists_uniformizer F v),
    WithZero.log_exp]
  norm_num

/-- The value-group coordinate of the uniformizer unit is the generator `1` of
the value group `Z`. -/
theorem finiteUniformizerUnit_valueGroup (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceValueMonoidHom v (finiteUniformizerUnit v) =
      Multiplicative.ofAdd (1 : ℤ) := by
  change Multiplicative.ofAdd (finitePlaceValueExponent v (finiteUniformizerUnit v)) =
    Multiplicative.ofAdd (1 : ℤ)
  rw [finiteUniformizerUnit_exponent]

/-- **Every integer exponent is realised by a global unit.**  The integer
powers of the uniformizer unit have all exponents. -/
theorem finitePlaceValueExponent_uniformizerUnit_zpow
    (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    finitePlaceValueExponent v (finiteUniformizerUnit v ^ n) = n := by
  have hmap := MonoidHom.map_zpow (finitePlaceValueMonoidHom v)
    (finiteUniformizerUnit v) n
  have hvalue : finitePlaceValueMonoidHom v (finiteUniformizerUnit v ^ n) =
      Multiplicative.ofAdd n := by
    rw [hmap, finiteUniformizerUnit_valueGroup, ← ofAdd_zsmul, zsmul_eq_mul, mul_one,
      Int.cast_id]
  have hto := congrArg Multiplicative.toAdd hvalue
  simpa [finitePlaceValueMonoidHom] using hto

/-- **The actual finite-place exponent is onto the integer value group.** -/
theorem finitePlaceValueExponent_surjective (v : HeightOneSpectrum (𝓞 F)) :
    Function.Surjective (finitePlaceValueExponent v) := by
  intro n
  exact ⟨finiteUniformizerUnit v ^ n,
    finitePlaceValueExponent_uniformizerUnit_zpow v n⟩

/-- **The actual finite value map of the global units has exactly the integer
line as image.** -/
theorem finiteValueMap_numberField_range (v : HeightOneSpectrum (𝓞 F)) :
    Set.range (finiteValueMap (numberFieldGlobalPlaceData (F := F)) v) =
      Set.range (fun k : ℤ => (k : ℝ)) := by
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨finitePlaceValueExponent v f, by rw [finiteValueMap_numberField]⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨f, hf⟩ := finitePlaceValueExponent_surjective v k
    exact ⟨f, by rw [finiteValueMap_numberField, hf]⟩

/-- **The realified image after scaling is exactly the integer lattice
`scale * Z`.**  At `scale = log q_v` this is the degree image
`Z * log q_v` (see `finiteValueMap_numberField_degreeImage`). -/
theorem finiteValueMap_numberField_scaled_range (v : HeightOneSpectrum (𝓞 F))
    (scale : ℝ) :
    Set.range (fun f : Fˣ => scale *
        finiteValueMap (numberFieldGlobalPlaceData (F := F)) v f) =
      Set.range (fun k : ℤ => scale * (k : ℝ)) := by
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨finitePlaceValueExponent v f, ?_⟩
    simp only [finiteValueMap_numberField]
  · rintro ⟨k, rfl⟩
    obtain ⟨f, hf⟩ := finitePlaceValueExponent_surjective v k
    refine ⟨f, ?_⟩
    simp only [finiteValueMap_numberField, hf]

/-- The actual degree image of the global units is the lattice
`Z * log q_v`, where `q_v = #(O_F / v)` is the residue-field cardinality. -/
theorem finiteValueMap_numberField_degreeImage (v : HeightOneSpectrum (𝓞 F)) :
    Set.range (fun f : Fˣ => Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))
        * finiteValueMap (numberFieldGlobalPlaceData (F := F)) v f) =
      Set.range (fun k : ℤ =>
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) * (k : ℝ)) :=
  finiteValueMap_numberField_scaled_range v _

/-- The composite `F^x -> (K_v)^x -> Gamma_v = Z` of the global units with
the value-group coordinate of the completion is onto the value group. -/
theorem finitePlaceGlobalUnitValue_valueGroup_surjective
    (v : HeightOneSpectrum (𝓞 F)) :
    Function.Surjective
      (fun f : Fˣ => finitePlaceLocalValue (F := F) v
        (finitePlaceGlobalUnitValue (F := F) v f)) := by
  intro n
  refine ⟨finiteUniformizerUnit v ^ (Multiplicative.toAdd n), ?_⟩
  dsimp only
  rw [finitePlaceLocalValue_apply, finitePlaceGlobalUnitValue_exponent,
    finitePlaceValueExponent_uniformizerUnit_zpow]
  exact ofAdd_toAdd n

/-! ## 2. Abstract refutation lemmas for the rational-image hypotheses -/

/-- If the image of a value map is an integer line, it cannot be the rational
line. -/
theorem not_valueMapRationalImage_of_integerRange {X : Type*}
    (ρ : X → ℝ) (h : Set.range ρ = Set.range (fun k : ℤ => (k : ℝ))) :
    ¬ LeanFormal.IUT.K1K2Realization.ValueMapRationalImage ρ := by
  intro hrat
  have hhalf : (1 / 2 : ℝ) ∈ Set.range (fun q : ℚ => (q : ℝ)) :=
    ⟨1 / 2, by norm_num⟩
  rw [← hrat] at hhalf
  rw [h] at hhalf
  obtain ⟨k, hk⟩ := hhalf
  have hk' : (k : ℝ) = 1 / 2 := hk
  have hzero : ((2 * k : ℤ) : ℝ) = 1 := by
    push_cast
    rw [hk']
    norm_num
  have hint : (2 * k : ℤ) = 1 := by exact_mod_cast hzero
  omega

/-- If the image of a value map scaled by a nonzero constant is a scaled
integer line, it cannot be the scaled rational line. -/
theorem not_valueMapScaledRationalImage_of_scaledIntegerRange {X : Type*}
    (ρ : X → ℝ) (scale : ℝ) (hscale : scale ≠ 0)
    (h : Set.range (fun x => scale * ρ x) =
      Set.range (fun k : ℤ => scale * (k : ℝ))) :
    ¬ LeanFormal.IUT.K1K2Realization.ValueMapScaledRationalImage scale ρ := by
  intro hrat
  have hhalf : scale * (1 / 2 : ℝ) ∈
      Set.range (fun q : ℚ => scale * (q : ℝ)) :=
    ⟨1 / 2, by norm_num⟩
  rw [← hrat] at hhalf
  rw [h] at hhalf
  obtain ⟨k, hk⟩ := hhalf
  have hk' : (k : ℝ) = 1 / 2 := mul_left_cancel₀ hscale hk
  have hzero : ((2 * k : ℤ) : ℝ) = 1 := by
    push_cast
    rw [hk']
    norm_num
  have hint : (2 * k : ℤ) = 1 := by exact_mod_cast hzero
  omega

/-! ## 3. The named range hypotheses of task-17 for the actual finite data -/

/-- **Refuted**: the actual finite value map of the global units does not have
rational image; its image is the integer line. -/
theorem not_finiteValueMapRationalImage_numberField (v : HeightOneSpectrum (𝓞 F)) :
    ¬ FiniteValueMapRationalImage (numberFieldGlobalPlaceData (F := F)) v :=
  not_valueMapRationalImage_of_integerRange _ (finiteValueMap_numberField_range v)

/-- **Refuted**: the degree-image hypothesis `Q * log q_v` fails for the
actual data at every nonzero scale; the actual degree image is the lattice
`Z * log q_v` (`finiteValueMap_numberField_degreeImage`). -/
theorem not_finiteDegreeImageHypothesis_numberField (v : HeightOneSpectrum (𝓞 F))
    (scale : ℝ) (hscale : scale ≠ 0) :
    ¬ FiniteDegreeImageHypothesis (numberFieldGlobalPlaceData (F := F)) v scale :=
  not_valueMapScaledRationalImage_of_scaledIntegerRange _
    scale hscale (finiteValueMap_numberField_scaled_range v scale)

/-- **Refuted** at the finite place: the unified value map does not have
rational image there (its finite component is the integer line). -/
theorem not_placeValueMapRationalImage_finite (v : HeightOneSpectrum (𝓞 F)) :
    ¬ PlaceValueMapRationalImage (numberFieldGlobalPlaceData (F := F)) (Sum.inl v) := by
  change ¬ LeanFormal.IUT.K1K2Realization.ValueMapRationalImage
    (finiteValueMap (numberFieldGlobalPlaceData (F := F)) v)
  exact not_finiteValueMapRationalImage_numberField v

/-- The range of the finite value kernel's degree is the image of the integer
line in `Multiplicative R`. -/
theorem finiteValueKernel_degree_range_numberField (v : HeightOneSpectrum (𝓞 F)) :
    Set.range (fun f : Fˣ =>
        (finiteValueKernel (numberFieldGlobalPlaceData (F := F)) v).degree f) =
      Set.range (fun k : ℤ => Multiplicative.ofAdd ((k : ℝ))) := by
  ext m
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨finitePlaceValueExponent v f, ?_⟩
    simp only [finiteValueKernel_degree_apply,
      numberFieldGlobalPlaceData_finiteDelta]
  · rintro ⟨k, rfl⟩
    obtain ⟨f, hf⟩ := finitePlaceValueExponent_surjective v k
    refine ⟨f, ?_⟩
    simp only [finiteValueKernel_degree_apply,
      numberFieldGlobalPlaceData_finiteDelta, hf]

/-! ## 4. The actual completion value group: onto `Z`, kernel `O_v^x` -/

/-- The realified value map of the actual `v`-adic completion units: the
classical exponent as a real number. -/
noncomputable def finitePlaceCompletionValueMap (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ → ℝ :=
  fun x => (completionValuationExponent v x : ℝ)

/-- The completion value map is the realified exponent. -/
theorem finitePlaceCompletionValueMap_apply (v : HeightOneSpectrum (𝓞 F))
    (x : (v.adicCompletion F)ˣ) :
    finitePlaceCompletionValueMap (F := F) v x =
      (completionValuationExponent v x : ℝ) :=
  rfl

/-- The completion value map is additive. -/
theorem finitePlaceCompletionValueMap_mul (v : HeightOneSpectrum (𝓞 F))
    (x y : (v.adicCompletion F)ˣ) :
    finitePlaceCompletionValueMap (F := F) v (x * y) =
      finitePlaceCompletionValueMap (F := F) v x +
        finitePlaceCompletionValueMap (F := F) v y := by
  rw [finitePlaceCompletionValueMap_apply, finitePlaceCompletionValueMap_apply,
    finitePlaceCompletionValueMap_apply, completionValuationExponent_mul]
  push_cast
  ring

/-- The completion value map vanishes at the unit. -/
theorem finitePlaceCompletionValueMap_one (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceCompletionValueMap (F := F) v 1 = 0 := by
  rw [finitePlaceCompletionValueMap_apply, completionValuationExponent_one]
  norm_num

/-- **The actual completion value map is onto `Z`.** -/
theorem finitePlaceCompletionValueMap_range (v : HeightOneSpectrum (𝓞 F)) :
    Set.range (finitePlaceCompletionValueMap (F := F) v) =
      Set.range (fun k : ℤ => (k : ℝ)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨completionValuationExponent v x, rfl⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨x, hx⟩ := completionValuationExponent_surjective (K := F) v k
    exact ⟨x, by rw [finitePlaceCompletionValueMap_apply, hx]⟩

/-- The scaled realified completion image is the lattice `scale * Z`. -/
theorem finitePlaceCompletionValueMap_scaled_range
    (v : HeightOneSpectrum (𝓞 F)) (scale : ℝ) :
    Set.range (fun x : (v.adicCompletion F)ˣ =>
        scale * finitePlaceCompletionValueMap (F := F) v x) =
      Set.range (fun k : ℤ => scale * (k : ℝ)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨completionValuationExponent v x, ?_⟩
    simp only [finitePlaceCompletionValueMap_apply]
  · rintro ⟨k, rfl⟩
    obtain ⟨x, hx⟩ := completionValuationExponent_surjective (K := F) v k
    refine ⟨x, ?_⟩
    simp only [finitePlaceCompletionValueMap_apply, hx]

/-- **The kernel of the actual completion value map is exactly the integral
units `O_v^x`.** -/
theorem finitePlaceCompletionValueMap_eq_zero_iff_mem_integralUnits
    (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    finitePlaceCompletionValueMap (F := F) v x = 0 ↔
      x ∈ (v.adicCompletionIntegers F).units := by
  rw [finitePlaceCompletionValueMap_apply, Int.cast_eq_zero]
  exact completionValuationExponent_eq_zero_iff_mem_integralUnits v x

/-- **Refuted**: the actual completion value map does not have rational image
(its image is the integer line). -/
theorem not_finitePlaceCompletionValueMap_rationalImage
    (v : HeightOneSpectrum (𝓞 F)) :
    ¬ LeanFormal.IUT.K1K2Realization.ValueMapRationalImage
      (finitePlaceCompletionValueMap (F := F) v) :=
  not_valueMapRationalImage_of_integerRange _
    (finitePlaceCompletionValueMap_range v)

/-- **Refuted** at every nonzero scale: the realified completion image is a
scaled integer lattice, not the scaled rational line. -/
theorem not_finitePlaceCompletionValueMap_scaledRationalImage
    (v : HeightOneSpectrum (𝓞 F)) (scale : ℝ) (hscale : scale ≠ 0) :
    ¬ LeanFormal.IUT.K1K2Realization.ValueMapScaledRationalImage scale
      (finitePlaceCompletionValueMap (F := F) v) :=
  not_valueMapScaledRationalImage_of_scaledIntegerRange _
    scale hscale (finitePlaceCompletionValueMap_scaled_range v scale)

/-- The range of the realified degree kernel on the completion units is the
lattice `Z * (-log q_v)`. -/
theorem finitePlaceUnitValueKernel_realification_range
    (v : HeightOneSpectrum (𝓞 F)) :
    Set.range (finitePlaceUnitValueKernel (F := F) v).realification =
      Set.range (fun k : ℤ =>
        -(Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))) * (k : ℝ)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨completionValuationExponent v x, ?_⟩
    rw [finitePlaceUnitValueKernel_realification]
    ring
  · rintro ⟨k, rfl⟩
    obtain ⟨x, hx⟩ := completionValuationExponent_surjective (K := F) v k
    refine ⟨x, ?_⟩
    rw [finitePlaceUnitValueKernel_realification, hx]
    ring

/-- **The local value-group structure, discharged**: the actual value-group
coordinate `(K_v)^x -> Gamma_v = Z` is surjective and has kernel exactly
`O_v^x`. -/
theorem finitePlaceLocalValue_range_and_kernel (v : HeightOneSpectrum (𝓞 F)) :
    Function.Surjective (finitePlaceLocalValue (F := F) v) ∧
      ∀ x : (v.adicCompletion F)ˣ,
        finitePlaceLocalValue (F := F) v x = 1 ↔
          x ∈ (v.adicCompletionIntegers F).units :=
  ⟨finitePlaceLocalValue_surjective v,
    fun x => finitePlaceLocalValue_eq_one_iff_mem_integralUnits v x⟩

/-! ## 5. The actual archimedean log image -/

/-- The global unit `2`. -/
noncomputable def twoUnit : Fˣ :=
  Units.mk0 (2 : F) (by norm_num)

/-- The global unit `2` has underlying field element `2`. -/
@[simp]
theorem twoUnit_coe : (twoUnit (F := F) : F) = 2 :=
  rfl

/-- An archimedean place sends `2` to `2`. -/
theorem infinitePlace_two (w : NumberField.InfinitePlace F) :
    w (2 : F) = 2 := by
  rw [← NumberField.InfinitePlace.norm_embedding_eq]
  rw [map_ofNat]
  norm_num

/-- An archimedean place sends `2^{-1}` to `2^{-1}`. -/
theorem infinitePlace_two_inv (w : NumberField.InfinitePlace F) :
    w ((2 : F)⁻¹) = (2 : ℝ)⁻¹ := by
  rw [map_inv₀, infinitePlace_two]

/-- The archimedean value of a global unit is `-log` of its archimedean
absolute value. -/
theorem infiniteValueMap_numberField_eq_neg_log (w : NumberField.InfinitePlace F)
    (f : Fˣ) :
    infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w f =
      -Real.log (w (f : F)) :=
  infiniteValueMap_numberField w f

/-- The map `x |-> -log x` used to state the actual archimedean log image. -/
def negLogReal (x : ℝ) : ℝ := -Real.log x

/-- The defining equation of the negated logarithm. -/
@[simp]
theorem negLogReal_apply (x : ℝ) : negLogReal x = -Real.log x :=
  rfl

/-- **The actual archimedean log image** is the image of the archimedean
absolute values under `-log`. -/
theorem infiniteValueMap_numberField_range (w : NumberField.InfinitePlace F) :
    Set.range (infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w) =
      negLogReal '' Set.range (fun f : Fˣ => w (f : F)) := by
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨w (f : F), ⟨f, rfl⟩, ?_⟩
    rw [negLogReal_apply, infiniteValueMap_numberField]
  · rintro ⟨x, ⟨f, rfl⟩, hxy⟩
    refine ⟨f, ?_⟩
    rw [infiniteValueMap_numberField]
    exact hxy

/-- The archimedean log value of the global unit `2` is `-log 2`. -/
theorem infiniteValueMap_two (w : NumberField.InfinitePlace F) :
    infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w (twoUnit (F := F)) =
      -Real.log 2 := by
  rw [infiniteValueMap_numberField]
  rw [twoUnit_coe, infinitePlace_two]

/-- The archimedean log value of the inverse global unit `2^{-1}` is
`log 2`. -/
theorem infiniteValueMap_two_inv (w : NumberField.InfinitePlace F) :
    infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w
        ((twoUnit (F := F))⁻¹) =
      Real.log 2 := by
  rw [infiniteValueMap_numberField]
  rw [show (((twoUnit (F := F))⁻¹ : Fˣ) : F) = ((2 : F))⁻¹ from rfl,
    map_inv₀, infinitePlace_two, Real.log_inv]
  ring

/-- The archimedean log value of the `n`-th power of `2` is
`-n log 2`. -/
theorem infiniteValueMap_two_pow (w : NumberField.InfinitePlace F) (n : ℕ) :
    infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w
        ((twoUnit (F := F)) ^ n) =
      -((n : ℝ) * Real.log 2) := by
  rw [infiniteValueMap_numberField]
  rw [Units.val_pow_eq_pow_val, map_pow,
    show w (twoUnit (F := F) : F) = 2 from by
      rw [twoUnit_coe, infinitePlace_two],
    Real.log_pow]

/-- The archimedean log value of the `n`-th power of `2^{-1}` is
`n log 2`. -/
theorem infiniteValueMap_two_inv_pow (w : NumberField.InfinitePlace F) (n : ℕ) :
    infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w
        (((twoUnit (F := F))⁻¹) ^ n) =
      (n : ℝ) * Real.log 2 := by
  rw [infiniteValueMap_numberField]
  rw [Units.val_pow_eq_pow_val, map_pow,
    show w (((twoUnit (F := F))⁻¹ : Fˣ) : F) = (2 : ℝ)⁻¹ from by
      rw [show (((twoUnit (F := F))⁻¹ : Fˣ) : F) = ((2 : F))⁻¹ from rfl,
        map_inv₀, infinitePlace_two],
    Real.log_pow, Real.log_inv]
  ring

/-- `-log 2` is in the actual archimedean log image. -/
theorem archimedean_log_two_mem_range (w : NumberField.InfinitePlace F) :
    -Real.log 2 ∈
      Set.range (infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w) :=
  ⟨twoUnit (F := F), infiniteValueMap_two w⟩

/-- `n log 2` is in the actual archimedean log image, for every `n`. -/
theorem archimedean_log_two_mul_mem_range (w : NumberField.InfinitePlace F)
    (n : ℕ) :
    (n : ℝ) * Real.log 2 ∈
      Set.range (infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w) :=
  ⟨((twoUnit (F := F))⁻¹) ^ n, infiniteValueMap_two_inv_pow w n⟩

/-- The actual archimedean log image is unbounded above. -/
theorem archimedean_log_image_unbounded_above (w : NumberField.InfinitePlace F) :
    ∀ B : ℝ, ∃ y ∈ Set.range (infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w),
      B < y := by
  intro B
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt (B / Real.log 2)
  refine ⟨(n : ℝ) * Real.log 2, archimedean_log_two_mul_mem_range w n, ?_⟩
  have hlt : B / Real.log 2 < (n : ℝ) := hn
  have := (div_lt_iff₀ hlog).mp hlt
  simpa [mul_comm] using this

/-- The archimedean value-group realification is surjective. -/
theorem archimedeanValueGroupKernel_realification_range :
    Set.range archimedeanValueGroupKernel.realification = Set.univ :=
  Set.range_eq_univ.mpr archimedeanValueGroupKernel_realification_surjective

/-- **Refuted at the value-group level**: the archimedean value-group
realification does not have rational image (its image is all of `R`, which
contains the irrational number `sqrt 2`).  This is a statement about the
value GROUP; no claim is made about the actual global-unit log image. -/
theorem archimedeanValueGroupKernel_not_rationalImage :
    ¬ LeanFormal.IUT.K1K2Realization.ValueMapRationalImage
      archimedeanValueGroupKernel.realification := by
  intro h
  have hmem : Real.sqrt 2 ∈ Set.range archimedeanValueGroupKernel.realification := by
    rw [archimedeanValueGroupKernel_realification_range]
    exact Set.mem_univ _
  rw [h] at hmem
  obtain ⟨q, hq⟩ := hmem
  exact (irrational_sqrt_two.ne_rat q) hq.symm

/-! ## 6. The exact remaining source statement (different carrier) -/

/-- Consumer restatement of the proved algebraic-closure rationality: for the
algebraically closed local field `(Qbar_p)^x` the normalized log-value image
is exactly `Q`.  This is a different carrier from the actual number-field
completion `K_v` or the global units `F^x` of this file. -/
theorem algebraicClosureValueGroup_rationalImage_consumer
    (p : ℕ) [Fact (Nat.Prime p)] :
    Set.range (fun u : (PadicAlgCl p)ˣ =>
        (LeanFormal.IUT.padicAlgClUnitLogVal p u).toAdd) =
      Set.range (fun q : ℚ => (q : ℝ)) :=
  LeanFormal.IUT.padicAlgCl_unit_logVal_range_eq_rat p

/-! ## 7. Exact status card -/

end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- **Value-group range/rationality status card for the actual place data.**

Proved (this module), for the actual number-field data of III Example 3.6:
the finite-place exponent of the global units is onto `Z`
(`finitePlaceValueExponent_surjective`), with range exactly the integer line;
the realified/scaled image is the lattice `Z * log q_v`
(`finiteValueMap_numberField_degreeImage`); the actual completion value map is
onto `Z` with kernel exactly `O_v^x`
(`finitePlaceCompletionValueMap_range`,
`finitePlaceCompletionValueMap_eq_zero_iff_mem_integralUnits`); the actual
archimedean log image is the `-log` image of the archimedean absolute values
(`infiniteValueMap_numberField_range`), containing `+- n log 2` and unbounded
above; and the archimedean value-GROUP realification is all of `R`, so not
rational.

Refuted for the actual data: `FiniteValueMapRationalImage`,
`FiniteDegreeImageHypothesis` (any nonzero scale), and
`PlaceValueMapRationalImage` at a finite place.  Not claimed:
`InfiniteValueMapRationalImage`, and `PlaceValueMapRationalImage` at an
archimedean place.

Remaining source statement (different carrier): the rational value group `Q`
and degree image `Q * log p` are proved for `(Qbar_p)^x` in
`PrimeStripFrobenioidValueGroupRationality` (restated as a consumer here).
Their transport to `F^x` or the discrete completion `K_v^x` -- i.e.
`v((Q_p)^x) = Q` for the global unit group -- is NOT available: the global
unit range is `Z`, and the `V_K`/`rho_v` vertical carrier that would
identify the two carriers is not constructed (boundary (2), task-27). -/
def example36ValueGroupRationality : Obligation :=
  { id := "IUT-I-II.example36-value-group-rationality"
    source :=
      "IUT I, Example 3.5, (i); IUT III, Example 3.6; boundary (2) value-group " ++
        "range/rationality row"
    status := VerificationStatus.provedKernel
    note :=
      "Proved: actual finite-place exponent onto Z (uniformizer powers), " ++
        "integer line as the finite global-unit value image, lattice Z * log " ++
        "q_v as the degree image, completion value map onto Z with kernel " ++
        "O_v^x, exact archimedean -log absolute-value image with +- n log 2 " ++
        "and unbounded above, and non-rationality of the archimedean " ++
        "value-group realification (image R, contains sqrt 2). Refuted for " ++
        "the actual data: FiniteValueMapRationalImage, " ++
        "FiniteDegreeImageHypothesis (nonzero scale), " ++
        "PlaceValueMapRationalImage at a finite place. Not claimed: " ++
        "InfiniteValueMapRationalImage and PlaceValueMapRationalImage at an " ++
        "archimedean place. Remaining source statement: the rational value " ++
        "group Q / degree image Q * log p is proved for the algebraically " ++
        "closed local field (Qbar_p)^x in " ++
        "PrimeStripFrobenioidValueGroupRationality; its transport to the " ++
        "global units F^x or the discrete completion K_v^x is not " ++
        "constructed (boundary (2) vertical carrier), so v((Q_p)^x) = Q for " ++
        "the global unit group is not claimed."
    dependsOn :=
      [ "IUT-II.prime-strips-frobenioid-value-group-rationality",
        "IUT-II.prime-strips-frobenioid-category-skeleton" ] }

end LeanFormal.IUT.Audit
