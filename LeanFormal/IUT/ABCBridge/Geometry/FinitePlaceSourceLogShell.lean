import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellScalarClosure
import LeanFormal.IUT.Foundations.LocalFields.LogarithmSeriesTransport

/-!
# The actual finite-place source log-shell

Construct `log : O_vˣ → K_v` on the project's actual completed number
field, using the proved normalized-norm and integer-ring equivalences.
Its scaled image is compact, open, contains the actual completed integer
ring, and is stable under p-adic integral scalars.

These are source objects for III Definition 1.1/Remark 1.2.2, not a
substitute for the remaining tensor/ind and poly-isomorphism arguments.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open scoped Valued

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The actual full unit groups are isomorphic, with no selected subgroup. -/
def normalizedCompletionUnitsEquiv (place : NumberField.FinitePlace K) :
    (Integers (NormalizedCompletion place))ˣ ≃* (CompletionIntegers place)ˣ :=
  Units.mapEquiv (normalizedCompletionIntegersEquiv place).toMulEquiv

/-- The logarithm of an actual integral unit in the actual completion. -/
def completionUnitLog (place : NumberField.FinitePlace K)
    (u : (CompletionIntegers place)ˣ) : Completion place :=
  normalizedCompletionRingEquiv place
    (unitLog ((normalizedCompletionUnitsEquiv place).symm u))

theorem completionUnitLog_one (place : NumberField.FinitePlace K) :
    completionUnitLog place 1 = 0 := by
  simp only [completionUnitLog, map_one,
    unitLog_one (p := (completionRationalPrime place).val), map_zero]

theorem completionUnitLog_mul (place : NumberField.FinitePlace K)
    (u v : (CompletionIntegers place)ˣ) :
    completionUnitLog place (u * v) = completionUnitLog place u + completionUnitLog place v := by
  simp only [completionUnitLog, map_mul,
    unitLog_mul (p := (completionRationalPrime place).val), map_add]

def completionUnitLogHom (place : NumberField.FinitePlace K) :
    (CompletionIntegers place)ˣ →* Multiplicative (Completion place) where
  toFun u := Multiplicative.ofAdd (completionUnitLog place u)
  map_one' := by
    change completionUnitLog place 1 = 0
    exact completionUnitLog_one place
  map_mul' u v := by
    change completionUnitLog place (u * v) = _
    exact completionUnitLog_mul place u v

theorem completionUnitLog_pow (place : NumberField.FinitePlace K)
    (u : (CompletionIntegers place)ˣ) (n : ℕ) :
    completionUnitLog place (u ^ n) = (n : Completion place) * completionUnitLog place u := by
  induction n with
  | zero => simp [completionUnitLog_one]
  | succ n ih =>
    rw [pow_succ, completionUnitLog_mul, ih]
    push_cast
    ring

/-- On actual principal units this is the actual canonical-completion
power-series logarithm, not merely a transported function with group laws. -/
theorem completionUnitLog_eq_log1p (place : NumberField.FinitePlace K)
    (u : (CompletionIntegers place)ˣ) (hu : ‖(u.val : Completion place) - 1‖ < 1) :
    completionUnitLog place u = log1p ((u.val : Completion place) - 1) := by
  let nu := (normalizedCompletionUnitsEquiv place).symm u
  have hoffset : normalizedCompletionRingEquiv place
      ((nu.val : NormalizedCompletion place) - 1) = (u.val : Completion place) - 1 := rfl
  have hnorm : ‖(nu.val : NormalizedCompletion place) - 1‖ < 1 :=
    (normalizedCompletion_norm_lt_one_iff place _).mp (by rw [hoffset]; exact hu)
  change normalizedCompletionRingEquiv place (unitLog nu) = _
  rw [unitLog_eq_log1p (p := (completionRationalPrime place).val) nu
    ((mem_principalUnits_iff _).mpr hnorm)]
  calc
    _ = log1p (normalizedCompletionRingEquiv place
        ((nu.val : NormalizedCompletion place) - 1)) :=
      log1p_map_of_continuous (p := (completionRationalPrime place).val)
        (normalizedCompletionRingEquiv place).toRingHom
        (normalizedCompletionHomeomorph place).continuous _ hnorm
    _ = _ := congrArg log1p hoffset

theorem continuous_completionUnitLog (place : NumberField.FinitePlace K) :
    Continuous (completionUnitLog place) := by
  have hu : Continuous (fun u : (CompletionIntegers place)ˣ =>
      (normalizedCompletionUnitsEquiv place).symm u) := by
    apply Units.continuous_iff.mpr
    constructor
    · exact (normalizedCompletionIntegersHomeomorph place).symm.continuous.comp
        Units.continuous_val
    · exact ((normalizedCompletionIntegersHomeomorph place).symm.continuous.comp
        Units.continuous_val).comp continuous_inv
  exact (normalizedCompletionHomeomorph place).continuous.comp
    ((continuous_unitLog (p := (completionRationalPrime place).val)).comp hu)

/-- The actual scaled logarithmic image as an additive subgroup of K_v. -/
def completionLogShell (place : NumberField.FinitePlace K) : AddSubgroup (Completion place) :=
  (integralLogShell (K := NormalizedCompletion place)
    (p := (completionRationalPrime place).val)).map
    (normalizedCompletionRingEquiv place).toAddMonoidHom

/-- The transported object is exactly `(p*)⁻¹ log(O_vˣ)` on actual units. -/
theorem completionLogShell_eq_unitLog_range (place : NumberField.FinitePlace K) :
    (completionLogShell place : Set (Completion place)) =
      Set.range (fun u : (CompletionIntegers place)ˣ =>
        (logShellScale (completionRationalPrime place).val : Completion place)⁻¹ *
          completionUnitLog place u) := by
  ext x
  constructor
  · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
    refine ⟨normalizedCompletionUnitsEquiv place u, ?_⟩
    change (logShellScale (completionRationalPrime place).val : Completion place)⁻¹ *
      completionUnitLog place (normalizedCompletionUnitsEquiv place u) =
      normalizedCompletionRingEquiv place
        ((logShellScale (completionRationalPrime place).val : NormalizedCompletion place)⁻¹ *
          unitLog u)
    simp only [completionUnitLog, MulEquiv.symm_apply_apply, map_mul, map_inv₀, map_natCast]
  · rintro ⟨u, rfl⟩
    refine ⟨_, ⟨(normalizedCompletionUnitsEquiv place).symm u, rfl⟩, ?_⟩
    change normalizedCompletionRingEquiv place
      ((logShellScale (completionRationalPrime place).val : NormalizedCompletion place)⁻¹ *
        unitLog ((normalizedCompletionUnitsEquiv place).symm u)) =
      (logShellScale (completionRationalPrime place).val : Completion place)⁻¹ *
        completionUnitLog place u
    simp only [completionUnitLog, map_mul, map_inv₀, map_natCast]

theorem isCompact_completionLogShell (place : NumberField.FinitePlace K) :
    IsCompact (completionLogShell place : Set (Completion place)) :=
  (isCompact_integralLogShell (K := NormalizedCompletion place)
    (p := (completionRationalPrime place).val)).image
    (normalizedCompletionHomeomorph place).continuous

/-- The unscaled actual unit logarithmic image is contained in its source
shell, as required on the codomain side of the log-link. -/
theorem completionUnitLog_mem_logShell (place : NumberField.FinitePlace K)
    (u : (CompletionIntegers place)ˣ) : completionUnitLog place u ∈ completionLogShell place := by
  rw [← SetLike.mem_coe, completionLogShell_eq_unitLog_range]
  refine ⟨u ^ logShellScale (completionRationalPrime place).val, ?_⟩
  dsimp only
  rw [completionUnitLog_pow]
  exact inv_mul_cancel_left₀
    (Nat.cast_ne_zero.mpr (ne_of_gt
      (logShellScale_pos (p := (completionRationalPrime place).val)))) _

/-- Every actual completed integer belongs to the constructed source shell. -/
theorem completionIntegers_subset_logShell (place : NumberField.FinitePlace K) :
    (CompletionIntegers place : Set (Completion place)) ⊆ completionLogShell place := by
  intro x hx
  let nx := (normalizedCompletionIntegersEquiv place).symm (⟨x, hx⟩ : CompletionIntegers place)
  refine ⟨(nx : NormalizedCompletion place),
    integers_subset_integralLogShell (p := (completionRationalPrime place).val) nx.property, ?_⟩
  exact congrArg Subtype.val ((normalizedCompletionIntegersEquiv place).apply_symm_apply ⟨x, hx⟩)

theorem isOpen_completionLogShell (place : NumberField.FinitePlace K) :
    IsOpen (completionLogShell place : Set (Completion place)) := by
  apply Metric.isOpen_iff.mpr
  intro x hx
  refine ⟨1, zero_lt_one, ?_⟩
  intro y hy
  have hnorm : ‖y - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hmem : y - x ∈ completionLogShell place :=
    completionIntegers_subset_logShell place
      ((mem_completionIntegers_iff_norm_le_one place _).mpr hnorm.le)
  change y ∈ completionLogShell place
  simpa only [sub_add_cancel] using (completionLogShell place).add_mem hmem hx

/-- Integral p-adic scalar stability on the actual completion carrier. -/
theorem completionLogShell_padicInt_mul_mem (place : NumberField.FinitePlace K)
    (z : ℤ_[(completionRationalPrime place).val]) {x : Completion place}
    (hx : x ∈ completionLogShell place) :
    padicCompletionHom place (z : PadicScalarField place) * x ∈ completionLogShell place := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨_, integralLogShell_padicInt_mul_mem z hy, ?_⟩
  change normalizedCompletionRingEquiv place
    (algebraMap (PadicScalarField place) (NormalizedCompletion place)
      (z : PadicScalarField place) * y) =
    padicCompletionHom place (z : PadicScalarField place) * normalizedCompletionRingEquiv place y
  rw [map_mul]
  rfl

end

end LeanFormal.IUT.NumberFieldFinitePlace
