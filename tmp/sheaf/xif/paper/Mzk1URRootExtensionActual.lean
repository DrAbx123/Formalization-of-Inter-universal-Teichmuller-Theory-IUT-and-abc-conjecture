/- U-R root carrier on the actual finite root extension (route §5.3 J1).

This file **reuses** the existing actual root-extension machinery
`PaperRootExtension*` instead of rebuilding it:

* `rootNormedExtension T b` (PaperRootCompletionTensorActual): the actual
  finite extension `L = K_b(r_b)` inside the actual normed algebraic closure,
  with `NontriviallyNormedField`, `FiniteDimensional` over `K_b` and `Q_p`,
  `IsUltrametricDist`, `CompleteSpace`, `ProperSpace`, `MeasurableSpace`/`BorelSpace`;
* `rootExtensionHaar` and `rootExtensionUnitBall` (PaperRootExtensionHaarActual),
  `rootHaarFactor` (PaperRootExtensionHaarFactorActual);
* `rootNormedUnit`, `rootNormedThetaValueInL` (root/theta data), and the actual
  root equation `sourceRoot_pow`.

New content: the interface for the q-pilot lane (`david`) — the actual root
element `urRootAlpha`, theta values `urRootTheta`, the real-valued order bridge
`urRootTheta_order`, and the actual normalized log-mass identity
`urRootMass_kummer` (instantiated from `Mzk1URRootMassActual`).

No sorry/axiom/True/PUnit, no heartbeat override, no completion root. -/
import tmp.sheaf.xif.paper.PaperRootExtensionHaarFactorActual
import tmp.sheaf.xif.paper.PaperRootExtensionUnitDecompositionActual
import tmp.sheaf.xif.paper.PaperRootExtensionNormBoundActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.Mzk1URRootMassActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.Mzk1URRootMassActual
open MeasureTheory
open scoped Pointwise

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual finite root extension carrier `L = K_b(r_b)` (reused donor). -/
abbrev urRootCarrier : Type := rootNormedExtension T b

/-- The actual root unit in `L` (reused donor). -/
abbrev urRootUnit : (urRootCarrier T b)ˣ := rootNormedUnit T b

/-- The actual root as a field element of `L`. -/
noncomputable def urRootAlpha : urRootCarrier T b :=
  ⟨rootNormedElement T b, rootNormedElement_mem T b⟩

theorem urRootAlpha_eq_unit : urRootAlpha T b = (rootNormedUnit T b : urRootCarrier T b) := rfl

theorem urRootAlpha_ne_zero : urRootAlpha T b ≠ 0 := by
  rw [urRootAlpha_eq_unit]
  exact Units.ne_zero (rootNormedUnit T b)

/-- The actual Kummer power relation in the actual root extension. -/
theorem urRootAlpha_pow :
    (urRootAlpha T b) ^ (2 * l.value) =
      algebraMap (rootBase T b) (urRootCarrier T b) ((sourceRootQUnit T b : rootBase T b)) := by
  apply Subtype.ext
  rw [IntermediateField.coe_algebraMap_apply]
  have hpow := rootNormedElement_pow T b
  change (rootNormedElement T b) ^ (2 * l.value) =
    algebraMap (rootBase T b) (rootNormedAmbient T b) ((qVFamily T b).q)
  rw [hpow]
  simp [sourceRootQUnit, unitToAlgClosed]

/-- The actual theta value in `L` (reused donor). -/
noncomputable def urRootTheta (j : SignedLabel l.value) : urRootCarrier T b :=
  rootNormedThetaValueInL T b j

/-- Real-valued order of a natural power, for any normed field. -/
theorem localNormOrder_pow_gen {M : Type*} [NormedField M] (p : ℕ) (n : ℕ) (x : M) :
    localNormOrder p (x ^ n) = (n : ℝ) * localNormOrder p x := by
  unfold localNormOrder
  rw [norm_pow, Real.log_pow]
  ring

/-- Real-valued order of an integer power, for any normed field. -/
theorem localNormOrder_zpow_gen {M : Type*} [NormedField M] (p : ℕ) (n : ℤ)
    (x : M) (hx : x ≠ 0) :
    localNormOrder p (x ^ n) = (n : ℝ) * localNormOrder p x := by
  unfold localNormOrder
  rw [norm_zpow, Real.log_zpow]
  ring

/-- **Order bridge (interface for the q-pilot lane).**  In the actual finite
root extension, `ord_p theta_j = (gaussExponent j / (2*l)) * ord_p q_b`. -/
theorem urRootTheta_order (j : SignedLabel l.value) :
    localNormOrder (qVFamTensorP T b) (urRootTheta T b j) =
      ((gaussExponent j.1 : ℝ) / (2 * (l.value : ℝ))) *
        localNormOrder (qVFamTensorP T b)
          (algebraMap (rootBase T b) (urRootCarrier T b) ((sourceRootQUnit T b : rootBase T b))) := by
  have halpha0 : urRootAlpha T b ≠ 0 := urRootAlpha_ne_zero T b
  have hord : localNormOrder (qVFamTensorP T b)
        (algebraMap (rootBase T b) (urRootCarrier T b) ((sourceRootQUnit T b : rootBase T b))) =
      (2 * (l.value : ℝ)) * localNormOrder (qVFamTensorP T b) (urRootAlpha T b) := by
    rw [← urRootAlpha_pow T b]
    rw [localNormOrder_pow_gen]
    push_cast
    ring
  have hval : urRootTheta T b j =
      (⟨rootNormedElement T b, rootNormedElement_mem T b⟩ : urRootCarrier T b) ^
        (gaussExponent j.1) := rfl
  have htheta : localNormOrder (qVFamTensorP T b) (urRootTheta T b j) =
      (gaussExponent j.1 : ℝ) * localNormOrder (qVFamTensorP T b) (urRootAlpha T b) := by
    rw [hval]
    rw [localNormOrder_zpow_gen (qVFamTensorP T b) (gaussExponent j.1)
      (⟨rootNormedElement T b, rootNormedElement_mem T b⟩ : urRootCarrier T b) halpha0]
    rfl
  rw [htheta, hord]
  have hl : (l.value : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < l.value := by
      exact_mod_cast (by have := l.ge_five; omega : 0 < l.value)
    positivity
  field_simp [hl]

/-- The root extension norm restricts the base norm along `algebraMap`. -/
theorem urRootCarrier_norm_algebraMap (x : rootBase T b) :
    ‖algebraMap (rootBase T b) (urRootCarrier T b) x‖ = ‖x‖ := by
  have h1 : ‖(algebraMap (rootBase T b) (urRootCarrier T b) x : urRootCarrier T b)‖ =
      ‖((algebraMap (rootBase T b) (urRootCarrier T b) x : rootNormedAmbient T b))‖ := rfl
  rw [h1, IntermediateField.coe_algebraMap_apply]
  exact norm_algebraMap' _ _

/-- The same order bridge on the actual `q_b` of the base field. -/
theorem urRootTheta_order_base (j : SignedLabel l.value) :
    localNormOrder (qVFamTensorP T b) (urRootTheta T b j) =
      ((gaussExponent j.1 : ℝ) / (2 * (l.value : ℝ))) *
        localNormOrder (qVFamTensorP T b) ((sourceRootQUnit T b : rootBase T b)) := by
  rw [urRootTheta_order]
  congr 1
  unfold localNormOrder
  rw [urRootCarrier_norm_algebraMap]

/-- Theta values are nonzero. -/
theorem urRootTheta_ne_zero (j : SignedLabel l.value) : urRootTheta T b j ≠ 0 := by
  have hval : urRootTheta T b j =
      (urRootAlpha T b) ^ (gaussExponent j.1) := rfl
  rw [hval]
  exact zpow_ne_zero _ (urRootAlpha_ne_zero T b)

/-- **Value form of the per-b theta pilot** (no finrank needed): the actual
log-norm of `theta_j` is `-ord_p(theta_j) * log p`. -/
theorem urRootTheta_log_norm_eq_neg_order (j : SignedLabel l.value) :
    Real.log ‖urRootTheta T b j‖ =
      -localNormOrder (qVFamTensorP T b) (urRootTheta T b j) *
        Real.log (qVFamTensorP T b : ℝ) := by
  unfold localNormOrder
  have hlogp : Real.log (qVFamTensorP T b : ℝ) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt)).ne'
  field_simp [hlogp]

/-- **Order value of the per-b theta pilot (route §5.2.2 shift)**: the actual
log-norm of `theta_j` is `-(gaussExponent j/(2l)) * ord_p(q_b) * log p`
(the actual C1 negative term on the root carrier; no finrank needed). -/
theorem urRootTheta_log_norm_eq_neg_shift (j : SignedLabel l.value) :
    Real.log ‖urRootTheta T b j‖ =
      -((gaussExponent j.1 : ℝ) / (2 * (l.value : ℝ))) *
        localNormOrder (qVFamTensorP T b) ((sourceRootQUnit T b : rootBase T b)) *
        Real.log (qVFamTensorP T b : ℝ) := by
  rw [urRootTheta_log_norm_eq_neg_order, urRootTheta_order_base]
  ring

/-- The same shift on `log ‖q_b‖` (theta is a `gaussExponent/(2l)`-power of `q_b`). -/
theorem urRootTheta_log_norm_eq_q (j : SignedLabel l.value) :
    Real.log ‖urRootTheta T b j‖ =
      ((gaussExponent j.1 : ℝ) / (2 * (l.value : ℝ))) *
        Real.log ‖((sourceRootQUnit T b : rootBase T b))‖ := by
  rw [urRootTheta_log_norm_eq_neg_shift]
  have hlog : Real.log ‖((sourceRootQUnit T b : rootBase T b))‖ =
      -localNormOrder (qVFamTensorP T b) ((sourceRootQUnit T b : rootBase T b)) *
        Real.log (qVFamTensorP T b : ℝ) := by
    unfold localNormOrder
    have hlogp : Real.log (qVFamTensorP T b : ℝ) ≠ 0 := by
      exact (Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt)).ne'
    field_simp [hlogp]
  rw [hlog]
  ring

/-- The global `Q_p`-normed-algebra structure on the actual root extension,
for consumers (q-pilot lane).  Uses the restricted-scalars algebra structure. -/
noncomputable instance urRootExtensionNormedAlgebra :
    NormedAlgebra ℚ_[qVFamTensorP T b] (rootNormedExtension T b) :=
  NormedAlgebra.restrictScalars ℚ_[qVFamTensorP T b] (rootBase T b) (rootNormedExtension T b)

#print axioms urRootAlpha_pow
#print axioms urRootTheta_order
#print axioms urRootTheta_order_base
#print axioms urRootTheta_log_norm_eq_neg_order
#print axioms urRootTheta_log_norm_eq_neg_shift
#print axioms urRootTheta_log_norm_eq_q

end LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
end