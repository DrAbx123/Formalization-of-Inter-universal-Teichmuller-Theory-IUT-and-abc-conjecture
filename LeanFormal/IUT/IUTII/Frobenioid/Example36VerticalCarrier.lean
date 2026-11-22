import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge
import LeanFormal.IUT.IUTII.Frobenioid.Example36ValueMapKernels
import LeanFormal.IUT.Audit.Status

set_option linter.unusedSectionVars false

/-!
# The real vertical value carrier over the completions (partial boundary (2))

Boundary (2), vertical-carrier fragment.  This module constructs the *real,
value-level* vertical carrier of the actual number-field completions: for every
finite place `v` the unit group `(K_v)^x` of the actual completion
`K_v = v.adicCompletion F`, the monoid homomorphism from the global units
`F^x`, the value coordinate `nu_v` onto the value group `Z`, the local
degree/realification `-nu * log #(O_F / v)`, and the reduced value kernels of
III Example 3.6 at `v`; for every archimedean place the analogous
absolute-value/log carrier.  The finite carriers are assembled into a dependent
family over all finite places, with pointwise compatibility with the
prime-strip value kernels of `Example36PrimeStripBridge` (task-21).

## What is constructed (actual completions only)

* `FinitePlaceVerticalCarrier v`: the completion units `(K_v)^x` with
  - `valueCoordinate : (K_v)^x ->* Z` (the classical exponent `nu_v`);
  - `valueCoordinate_surjective`, with kernel exactly the integral units
    `O_v^x` (surjectivity and kernel are those of the actual completion
    valuation, `Example36LocalIdealValuation`);
  - `globalToLocal : F^x ->* (K_v)^x`, the actual embedding of global units,
    whose value coordinate is `finitePlaceValueExponent` (equivalently the
    completion exponent of the embedded unit);
  - `degree : (K_v)^x ->* Multiplicative R` with realification
    `Multiplicative.toAdd (degree x) = -nu_v(x) * log #(O_F / v)`;
  - the reduced value kernels `kernel` (on `(K_v)^x`) and `groupKernel`
    (on the value group `Z`) with their degree/realification laws.
* `finitePlaceVerticalCarrier v`: the carrier filled by the actual objects
  (`finitePlaceLocalValue`, `finitePlaceGlobalUnitValue`,
  `finitePlaceLocalDegree`, `finitePlaceUnitValueKernel`,
  `finitePlaceValueGroupKernel` of `Example36PrimeStripBridge`).
* Per-place compatibility with the prime-strip value kernels of task-21: the
  carrier's kernel is the task-21 kernel, its degree is the task-21 local
  degree, its group kernel is the task-21 value-group kernel, and the realified
  degree of an embedded global unit is the task-21 realification
  `-finitePlaceValueExponent * log q_v` (equivalently
  `completionValuationAdd * log q_v`).
* `finitePlaceVerticalCarrierFamily`: the dependent family over all finite
  places with the pointwise global-to-local maps and per-place compatibility.
* `ArchimedeanVerticalCarrier w`: the analogous carrier at an archimedean
  place: the actual absolute value `w`, the local value map
  `-log (w f)` on global units, the value-group kernel with identity degree,
  and the surjective realification; the realification of a global unit is the
  `infiniteDelta`/archimedean value of the Example 3.6 data.
* `LeanFormal.IUT.Audit.example36VerticalValueCarrier`: the exact status card
  (interface) recording what is missing for the source `V_K`/`rho_v`
  carrier.

## What is missing for the source V_K/rho_v carrier (no source claim)

The source vertical carrier is not constructed here.  Missing are, exactly:
the source-level identification of the value group with the rational group
`(Qbar_p)^x` (the actual completion `K_v` has value group `Z`; see the
task-35 card), the normalization isomorphism
`rho_v = 1/[K_v:(F_mod)_v] * logPhi(pv)` of IUT I Example 3.5 (i), the
log-shell carrier, and the Frobenius/log-Kummer carrier on the vertical
values.  Consequently no source-faithfulness claim is made, and no
identity/constant substitution is used: all arrows above are the actual
completion/valuation maps of the tree.

## Boundary

No theta-pilot, q-pilot, Tate or Hodge-theater claim.  The carrier is the real
value-level carrier over the actual completions only; the `V_K` transport and
the `rho_v` normalization remain open (card).
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. The finite-place vertical value carrier over the actual completion -/

/-- The unit group of the actual `v`-adic completion `K_v`, the local unit
carrier of the vertical value datum. -/
abbrev finitePlaceCompletionUnits (v : HeightOneSpectrum (𝓞 F)) : Type u :=
  (v.adicCompletion F)ˣ

/-- The actual finite-place vertical value carrier at `v`: the completion
units, the global-to-local map, the value coordinate, the local degree and the
reduced value kernels of the Example 3.6 data.  All fields are the actual
completion/valuation objects; no source object is claimed. -/
structure FinitePlaceVerticalCarrier (v : HeightOneSpectrum (𝓞 F)) where
  /-- The value coordinate `(K_v)^x -> Gamma_v = Z`: the classical exponent. -/
  valueCoordinate : finitePlaceCompletionUnits (F := F) v →* Multiplicative ℤ
  /-- The value coordinate is onto the value group. -/
  valueCoordinate_surjective : Function.Surjective valueCoordinate
  /-- The kernel of the value coordinate is exactly the integral units. -/
  valueCoordinate_kernel : ∀ x : finitePlaceCompletionUnits (F := F) v,
    valueCoordinate x = 1 ↔ x ∈ (v.adicCompletionIntegers F).units
  /-- The actual map from the global units into the completion units. -/
  globalToLocal : Fˣ →* finitePlaceCompletionUnits (F := F) v
  /-- The value coordinate of an embedded global unit is its integer exponent. -/
  global_value : ∀ f : Fˣ, valueCoordinate (globalToLocal f) =
    Multiplicative.ofAdd (finitePlaceValueExponent v f)
  /-- The local degree of a completion unit, normalized by the residue-field
  cardinality. -/
  degree : finitePlaceCompletionUnits (F := F) v →* Multiplicative ℝ
  /-- The reduced value kernel on the completion units. -/
  kernel : LeanFormal.IUT.FrobenioidValueKernel (finitePlaceCompletionUnits (F := F) v)
  /-- The kernel degree is the local degree. -/
  kernel_degree : kernel.degree = degree
  /-- The kernel realification is the additive form of the degree. -/
  kernel_realification : ∀ x : finitePlaceCompletionUnits (F := F) v,
    kernel.realification x = Multiplicative.toAdd (degree x)
  /-- The reduced value kernel on the value group `Gamma_v = Z`. -/
  groupKernel : LeanFormal.IUT.FrobenioidValueKernel (Multiplicative ℤ)
  /-- The value-group kernel degree is the value-group degree. -/
  groupKernel_degree : groupKernel.degree = finitePlaceValueGroupDegree (F := F) v

/-- The actual finite-place vertical value carrier, filled by the actual
completion valuation, the actual embedding of global units, the actual
normalized local degree and the task-21 reduced value kernels. -/
noncomputable def finitePlaceVerticalCarrier
    (v : HeightOneSpectrum (𝓞 F)) : FinitePlaceVerticalCarrier (F := F) v where
  valueCoordinate := finitePlaceLocalValue (F := F) v
  valueCoordinate_surjective := finitePlaceLocalValue_surjective (F := F) v
  valueCoordinate_kernel := fun x =>
    finitePlaceLocalValue_eq_one_iff_mem_integralUnits (F := F) v x
  globalToLocal := finitePlaceGlobalUnitValue (F := F) v
  global_value := fun f => by
    rw [finitePlaceLocalValue_apply, finitePlaceGlobalUnitValue_exponent]
  degree := finitePlaceLocalDegree (F := F) v
  kernel := finitePlaceUnitValueKernel (F := F) v
  kernel_degree := rfl
  kernel_realification := fun x => rfl
  groupKernel := finitePlaceValueGroupKernel (F := F) v
  groupKernel_degree := rfl

/-- The value coordinate of the carrier is the actual local value map. -/
@[simp]
theorem finitePlaceVerticalCarrier_valueCoordinate
    (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlaceVerticalCarrier (F := F) v).valueCoordinate =
      finitePlaceLocalValue (F := F) v :=
  rfl

/-- The global-to-local map of the carrier is the actual embedding of global
units into the completion units. -/
@[simp]
theorem finitePlaceVerticalCarrier_globalToLocal
    (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlaceVerticalCarrier (F := F) v).globalToLocal =
      finitePlaceGlobalUnitValue (F := F) v :=
  rfl

/-- The local degree of the carrier is the task-21 normalized local degree. -/
@[simp]
theorem finitePlaceVerticalCarrier_degree (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlaceVerticalCarrier (F := F) v).degree =
      finitePlaceLocalDegree (F := F) v :=
  rfl

/-- The reduced value kernel of the carrier is the task-21 unit-value kernel. -/
@[simp]
theorem finitePlaceVerticalCarrier_kernel (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlaceVerticalCarrier (F := F) v).kernel =
      finitePlaceUnitValueKernel (F := F) v :=
  rfl

/-- The value-group kernel of the carrier is the task-21 value-group kernel. -/
@[simp]
theorem finitePlaceVerticalCarrier_groupKernel (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlaceVerticalCarrier (F := F) v).groupKernel =
      finitePlaceValueGroupKernel (F := F) v :=
  rfl

/-- The value coordinate of a completion unit is its classical exponent. -/
theorem finitePlaceVerticalCarrier_valueCoordinate_apply
    (v : HeightOneSpectrum (𝓞 F)) (x : finitePlaceCompletionUnits (F := F) v) :
    (finitePlaceVerticalCarrier (F := F) v).valueCoordinate x =
      Multiplicative.ofAdd (completionValuationExponent v x) := by
  rw [finitePlaceVerticalCarrier_valueCoordinate, finitePlaceLocalValue_apply]

/-- The value coordinate of an embedded global unit is the actual
finite-place exponent. -/
theorem finitePlaceVerticalCarrier_value_global
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlaceVerticalCarrier (F := F) v).valueCoordinate
        ((finitePlaceVerticalCarrier (F := F) v).globalToLocal f) =
      Multiplicative.ofAdd (finitePlaceValueExponent v f) :=
  (finitePlaceVerticalCarrier (F := F) v).global_value f

/-- The value coordinate of an embedded global unit is the completion exponent
of its image in `K_v`. -/
theorem finitePlaceVerticalCarrier_value_global_completion
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlaceVerticalCarrier (F := F) v).valueCoordinate
        ((finitePlaceVerticalCarrier (F := F) v).globalToLocal f) =
      Multiplicative.ofAdd
        (completionValuationExponent v (finitePlaceGlobalUnitValue (F := F) v f)) := by
  rw [finitePlaceVerticalCarrier_value_global, finitePlaceGlobalUnitValue_exponent]

/-- The value coordinate of the embedded global units is exactly the task-21
finite local value data `delta`: per-place compatibility of the carrier with
the Example 3.6 finite local value map. -/
theorem numberFieldFiniteLocalValueData_eq_verticalCarrierValue
    (v : HeightOneSpectrum (𝓞 F)) :
    (numberFieldFiniteLocalValueData (F := F) v).delta =
      ((finitePlaceVerticalCarrier (F := F) v).valueCoordinate).comp
        ((finitePlaceVerticalCarrier (F := F) v).globalToLocal) := by
  rw [finitePlaceVerticalCarrier_valueCoordinate, finitePlaceVerticalCarrier_globalToLocal]
  exact numberFieldFiniteLocalValueData_delta_eq_primeStripValue (F := F) v

/-- **Realified degree of an embedded global unit**: the negated integer
exponent times `log #(O_F / v)`, i.e. the task-21 realification of the
prime-strip value kernel. -/
theorem finitePlaceVerticalCarrier_kernel_realification_global
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlaceVerticalCarrier (F := F) v).kernel.realification
        ((finitePlaceVerticalCarrier (F := F) v).globalToLocal f) =
      -((finitePlaceValueExponent v f : ℝ)) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  rw [finitePlaceVerticalCarrier_kernel, finitePlaceVerticalCarrier_globalToLocal]
  exact finitePlaceUnitValueKernel_realification_globalUnit (F := F) v f

/-- The same realified degree in the logarithm form of the completion
valuation: `completionValuationAdd * log #(O_F / v)`. -/
theorem finitePlaceVerticalCarrier_kernel_realification_global_valuationLog
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlaceVerticalCarrier (F := F) v).kernel.realification
        ((finitePlaceVerticalCarrier (F := F) v).globalToLocal f) =
      completionValuationAdd v (finitePlaceGlobalUnitValue (F := F) v f) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  rw [finitePlaceVerticalCarrier_kernel, finitePlaceVerticalCarrier_globalToLocal]
  exact finitePlaceUnitValueKernel_realification_eq_valuationLog (F := F) v
    (finitePlaceGlobalUnitValue (F := F) v f)

/-- The realified local degree of an embedded global unit, read from the
carrier's degree map: `-nu * log #(O_F / v)`. -/
theorem finitePlaceVerticalCarrier_degree_global
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    Multiplicative.toAdd
        ((finitePlaceVerticalCarrier (F := F) v).degree
          ((finitePlaceVerticalCarrier (F := F) v).globalToLocal f)) =
      -((finitePlaceValueExponent v f : ℝ)) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  rw [finitePlaceVerticalCarrier_degree, finitePlaceLocalDegree_apply]
  rw [finitePlaceVerticalCarrier_globalToLocal, finitePlaceGlobalUnitValue_exponent]
  rw [toAdd_ofAdd]

/-- **Per-place compatibility with the task-21 value kernels**, bundled: the
carrier's value coordinate, degree, unit-value kernel and value-group kernel
are exactly the prime-strip objects of `Example36PrimeStripBridge`. -/
theorem finitePlaceVerticalCarrier_compat_primeStrip
    (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlaceVerticalCarrier (F := F) v).valueCoordinate =
        finitePlaceLocalValue (F := F) v ∧
      (finitePlaceVerticalCarrier (F := F) v).globalToLocal =
        finitePlaceGlobalUnitValue (F := F) v ∧
      (finitePlaceVerticalCarrier (F := F) v).degree =
        finitePlaceLocalDegree (F := F) v ∧
      (finitePlaceVerticalCarrier (F := F) v).kernel =
        finitePlaceUnitValueKernel (F := F) v ∧
      (finitePlaceVerticalCarrier (F := F) v).groupKernel =
        finitePlaceValueGroupKernel (F := F) v :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The value-group kernel of the carrier realifies through the value-group
degree: `-n * log #(O_F / v)`. -/
theorem finitePlaceVerticalCarrier_groupKernel_realification
    (v : HeightOneSpectrum (𝓞 F)) (n : Multiplicative ℤ) :
    (finitePlaceVerticalCarrier (F := F) v).groupKernel.realification n =
      -(((Multiplicative.toAdd n : ℤ) : ℝ)) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  rw [finitePlaceVerticalCarrier_groupKernel,
    finitePlaceValueGroupKernel_realification]

/-! ## 2. The dependent family over all finite places -/

/-- The dependent family of actual finite-place vertical value carriers over
all finite places of the number field. -/
noncomputable def finitePlaceVerticalCarrierFamily :
    (v : HeightOneSpectrum (𝓞 F)) → FinitePlaceVerticalCarrier (F := F) v :=
  fun v => finitePlaceVerticalCarrier (F := F) v

/-- A member of the family is the actual carrier at the place. -/
@[simp]
theorem finitePlaceVerticalCarrierFamily_apply
    (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceVerticalCarrierFamily (F := F) v =
      finitePlaceVerticalCarrier (F := F) v :=
  rfl

/-- Pointwise global-to-local value compatibility for the family: at every
finite place the value coordinate of the embedded global unit is its actual
integer exponent. -/
theorem finitePlaceVerticalCarrierFamily_value_global
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlaceVerticalCarrierFamily (F := F) v).valueCoordinate
        ((finitePlaceVerticalCarrierFamily (F := F) v).globalToLocal f) =
      Multiplicative.ofAdd (finitePlaceValueExponent v f) :=
  (finitePlaceVerticalCarrierFamily (F := F) v).global_value f

/-- Pointwise realified-degree compatibility for the family: at every finite
place the realified degree of the embedded global unit is
`-nu_v(f) * log #(O_F / v)`. -/
theorem finitePlaceVerticalCarrierFamily_kernel_realification_global
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlaceVerticalCarrierFamily (F := F) v).kernel.realification
        ((finitePlaceVerticalCarrierFamily (F := F) v).globalToLocal f) =
      -((finitePlaceValueExponent v f : ℝ)) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) :=
  finitePlaceVerticalCarrier_kernel_realification_global v f

/-! ## 3. The archimedean analogue of the vertical carrier -/

/-- The archimedean vertical value carrier at `w`: the actual absolute value
`w`, the local value map `-log (w f)` on the global units, and the
value-group kernel with identity degree. -/
structure ArchimedeanVerticalCarrier (w : NumberField.InfinitePlace F) where
  /-- The local value map on the global units, into the archimedean value
  group `Multiplicative R`. -/
  localValue : Fˣ →* Multiplicative ℝ
  /-- The additive realification of the local value is the actual
  `-log (w f)`. -/
  localValue_realification : ∀ f : Fˣ,
    Multiplicative.toAdd (localValue f) = archimedeanPlaceValue w f
  /-- The value-group kernel at the archimedean place. -/
  kernel : LeanFormal.IUT.FrobenioidValueKernel (Multiplicative ℝ)
  /-- The kernel realification is the additive form of the value. -/
  kernel_realification : ∀ r : Multiplicative ℝ,
    kernel.realification r = Multiplicative.toAdd r
  /-- The kernel degree is the identity on the archimedean value group. -/
  kernel_degree : kernel.degree = MonoidHom.id (Multiplicative ℝ)
  /-- The realification is surjective onto `R`. -/
  realification_surjective : Function.Surjective kernel.realification

/-- The actual archimedean vertical carrier, filled by the actual
archimedean principal value and the task-21 archimedean value kernel. -/
noncomputable def archimedeanVerticalCarrier
    (w : NumberField.InfinitePlace F) : ArchimedeanVerticalCarrier (F := F) w where
  localValue := archimedeanPlaceValueUnit (F := F) w
  localValue_realification := fun _ => rfl
  kernel := archimedeanValueGroupKernel
  kernel_realification := fun _ => rfl
  kernel_degree := rfl
  realification_surjective :=
    archimedeanValueGroupKernel_realification_surjective

/-- The local value map of the archimedean carrier is the actual archimedean
principal value map. -/
@[simp]
theorem archimedeanVerticalCarrier_localValue
    (w : NumberField.InfinitePlace F) :
    (archimedeanVerticalCarrier (F := F) w).localValue =
      archimedeanPlaceValueUnit (F := F) w :=
  rfl

/-- The value-group kernel of the archimedean carrier is the task-21
archimedean value kernel. -/
@[simp]
theorem archimedeanVerticalCarrier_kernel
    (w : NumberField.InfinitePlace F) :
    (archimedeanVerticalCarrier (F := F) w).kernel =
      archimedeanValueGroupKernel :=
  rfl

/-- The archimedean realification of a global unit is the actual
`-log (w f)`. -/
theorem archimedeanVerticalCarrier_realification_global
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    (archimedeanVerticalCarrier (F := F) w).kernel.realification
        ((archimedeanVerticalCarrier (F := F) w).localValue f) =
      -Real.log (w (f : F)) := by
  rw [archimedeanVerticalCarrier_kernel, archimedeanVerticalCarrier_localValue]
  exact archimedeanValueGroupKernel_realification_globalUnit (F := F) w f

/-- The archimedean realification of a global unit is its `infiniteDelta` in
the packaged global place data. -/
theorem archimedeanVerticalCarrier_infiniteDelta_global
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    (archimedeanVerticalCarrier (F := F) w).kernel.realification
        ((archimedeanVerticalCarrier (F := F) w).localValue f) =
      (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w := by
  rw [archimedeanVerticalCarrier_realification_global,
    numberFieldGlobalPlaceData_infiniteDelta]

/-- The archimedean realification of a global unit is the actual value map of
`Example36ValueMapKernels`. -/
theorem archimedeanVerticalCarrier_infiniteValueMap_global
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    (archimedeanVerticalCarrier (F := F) w).kernel.realification
        ((archimedeanVerticalCarrier (F := F) w).localValue f) =
      infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w f := by
  rw [archimedeanVerticalCarrier_infiniteDelta_global,
    infiniteValueMap_apply]

/-- **Per-place compatibility of the archimedean carrier with the task-21
archimedean value kernel**, bundled. -/
theorem archimedeanVerticalCarrier_compat_primeStrip
    (w : NumberField.InfinitePlace F) :
    (archimedeanVerticalCarrier (F := F) w).localValue =
        archimedeanPlaceValueUnit (F := F) w ∧
      (archimedeanVerticalCarrier (F := F) w).kernel =
        archimedeanValueGroupKernel ∧
      (∀ r : Multiplicative ℝ,
        (archimedeanVerticalCarrier (F := F) w).kernel.realification r =
          Multiplicative.toAdd r) :=
  ⟨rfl, rfl, fun r => (archimedeanVerticalCarrier (F := F) w).kernel_realification r⟩

/-! ## 4. Exact status card for the missing source V_K/rho_v carrier -/

end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- **Exact status card for the partial vertical value carrier.**

Constructed (this module, from actual completions only): for every finite
place `v` the vertical carrier on the actual completion units `(K_v)^x`
with the value coordinate `nu_v` onto `Z` (surjective, kernel `O_v^x`),
the actual global-to-local monoid hom `F^x -> (K_v)^x` whose value
coordinate is `finitePlaceValueExponent` (equivalently the completion
exponent of the embedded unit), the local degree/realification
`-nu * log #(O_F / v)`, and the reduced value kernels, assembled into the
dependent family `finitePlaceVerticalCarrierFamily` with pointwise
compatibility with the task-21 prime-strip value kernels; and the archimedean
analogue `ArchimedeanVerticalCarrier w` on the actual absolute value, whose
realification is `-log (w f)` (the `infiniteDelta` of the Example 3.6 data),
also compatible with the task-21 archimedean value kernel.

Missing for the source `V_K`/`rho_v` vertical carrier (NOT constructed,
NOT claimed): the source-level identification of the value group with the
rational group `(Qbar_p)^x` (the actual completion has value group `Z`;
see `IUT-I-II.example36-value-group-rationality`), the normalization
isomorphism `rho_v = 1/[K_v:(F_mod)_v] * logPhi(pv)` of IUT I Example 3.5
(i), the log-shell carrier, and the Frobenius/log-Kummer carrier on the
vertical values.  No source-faithfulness claim; no identity or constant
substitution is used. -/
def example36VerticalValueCarrier : Obligation :=
  { id := "IUT-I-II.example36-vertical-value-carrier"
    source :=
      "IUT I, Example 3.5, (i); IUT III, Example 3.6; boundary (2) V_K/rho_v " ++
        "vertical-carrier row"
    status := VerificationStatus.interface
    note :=
      "Constructed: actual finite-place vertical carriers on the completion " ++
        "units K_v^x with value coordinate nu_v onto Z (surjective, kernel " ++
        "O_v^x), actual global-to-local monoid hom F^x -> K_v^x with value " ++
        "coordinate finitePlaceValueExponent (equivalently the completion " ++
        "exponent of the embedded unit), local degree/realification " ++
        "-nu * log #(O_F / v), reduced value kernels, dependent family over " ++
        "all finite places with per-place compatibility with the task-21 " ++
        "prime-strip value kernels; archimedean analogue on the actual " ++
        "absolute value with realification -log (w f) = infiniteDelta, " ++
        "compatible with the task-21 archimedean value kernel. Missing for " ++
        "the source V_K/rho_v carrier: the source-level identification of " ++
        "the value group with the rational group (Qbar_p)^x (actual " ++
        "completion value group is Z), the normalization rho_v = " ++
        "1/[K_v:(F_mod)_v] * logPhi(pv), the log-shell carrier, and the " ++
        "Frobenius/log-Kummer carrier. No source-faithfulness claim."
    dependsOn :=
      [ "IUT-I-II.example36-value-map-prime-strip-transport",
        "IUT-I-II.example36-value-group-rationality",
        "IUT-II.prime-strips-frobenioid-category-skeleton" ] }

end LeanFormal.IUT.Audit
