/- U-R actual root carrier: global `Q_p`-instances on the actual finite root
extension and the per-b theta mass theorems consumed by the q-pilot lane
(route §5.2.2 / §5.3 J1, C1 negative term = actual theta order).

The `FiniteDimensional ℚ_p F_b` instance is pinned to the **same** `Module`
instance as the normed-algebra structure, so consumers do not hit the donor
`NormedSpace`/`NormedAlgebra` module diamond.

This file only adds instances and the two per-b mass identities; it reuses
`Mzk1URRootExtensionActual` / `Mzk1ULThetaPacketActual.ulNormalizedLogMass_smul`.
No sorry/axiom/True/PUnit, no heartbeat override. -/
import tmp.sheaf.xif.paper.Mzk1URRootExtensionActual
import tmp.sheaf.xif.paper.Mzk1ULThetaPacketActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual

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
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1ULThetaPacketActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootMassActual
open MeasureTheory
open scoped Pointwise

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The `Q_p`-algebra structure on the actual root extension used by the
normalized log-mass theorem (restricted scalars through `K_b`). -/
noncomputable instance urRootExtensionAlgebraQp :
    Algebra ℚ_[qVFamTensorP T b] (rootNormedExtension T b) :=
  Algebra.restrictScalars ℚ_[qVFamTensorP T b] (rootBase T b) (rootNormedExtension T b)

/-- The `Q_p`-normed-algebra structure (same algebra). -/
noncomputable instance urRootExtensionNormedAlgebraQp :
    NormedAlgebra ℚ_[qVFamTensorP T b] (rootNormedExtension T b) :=
  NormedAlgebra.restrictScalars ℚ_[qVFamTensorP T b] (rootBase T b) (rootNormedExtension T b)

/-- The `Q_p`-module structure pinned to the normed-algebra's module, so the
carrier has a unique `Q_p`-module (no donor/consumer diamond). -/
noncomputable instance (priority := 1100) urRootExtensionModuleQp :
    Module ℚ_[qVFamTensorP T b] (rootNormedExtension T b) :=
  Algebra.toModule

/-- The `Q_p ⊆ K_b ⊆ F_b` scalar tower for the pinned module. -/
noncomputable instance (priority := 1100) urRootExtensionTowerQp :
    IsScalarTower ℚ_[qVFamTensorP T b] (rootBase T b) (rootNormedExtension T b) where
  smul_assoc r k x := by
    simp only [Algebra.smul_def, map_mul]
    rw [show (algebraMap ℚ_[qVFamTensorP T b] (rootNormedExtension T b)) r =
        (algebraMap (rootBase T b) (rootNormedExtension T b))
          ((algebraMap ℚ_[qVFamTensorP T b] (rootBase T b)) r) from rfl]
    ring

/-- Finite `Q_p`-degree with the pinned module. -/
noncomputable instance urRootExtensionFiniteDimQp :
    FiniteDimensional ℚ_[qVFamTensorP T b] (rootNormedExtension T b) := by
  haveI : FiniteDimensional (rootBase T b) (rootNormedExtension T b) :=
    rootNormedExtensionFiniteDimensional (T := T) (b := b)
  exact FiniteDimensional.trans ℚ_[qVFamTensorP T b] (rootBase T b) (rootNormedExtension T b)

/-- **Per-b theta mass** (q-pilot (2)): the finrank-normalized Haar log-mass of the
actual theta principal lattice is `log ‖theta_j‖`. -/
theorem urRootTheta_mass (j : SignedLabel l.value) :
    (1 / (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : ℝ)) *
      (Real.log (rootExtensionHaar T b
          ((urRootTheta T b j) • (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b)))).toReal -
        Real.log (rootExtensionHaar T b
          (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b))).toReal) =
      Real.log ‖urRootTheta T b j‖ :=
  ulNormalizedLogMass_smul (p := qVFamTensorP T b)
    (L := rootNormedExtension T b) (rootExtensionHaar T b)
    (urRootTheta T b j) (urRootTheta_ne_zero T b j)

/-- **Per-b theta mass in the C1 negative-order form** (q-pilot (3)). -/
theorem urRootTheta_mass_neg_order (j : SignedLabel l.value) :
    (1 / (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : ℝ)) *
      (Real.log (rootExtensionHaar T b
          ((urRootTheta T b j) • (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b)))).toReal -
        Real.log (rootExtensionHaar T b
          (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b))).toReal) =
      -localNormOrder (qVFamTensorP T b) (urRootTheta T b j) *
        Real.log (qVFamTensorP T b : ℝ) := by
  rw [urRootTheta_mass, urRootTheta_log_norm_eq_neg_order]

/-- The actual q-side log-norm on the root carrier: `log ‖q_b‖ = -ord_p(q_b) log p`. -/
theorem urRootQ_log_norm_order :
    Real.log ‖((sourceRootQUnit T b : rootBase T b))‖ =
      -localNormOrder (qVFamTensorP T b) ((sourceRootQUnit T b : rootBase T b)) *
        Real.log (qVFamTensorP T b : ℝ) := by
  unfold localNormOrder
  have hlogp : Real.log (qVFamTensorP T b : ℝ) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt)).ne'
  field_simp [hlogp]

/-- **Actual per-b `urRootAlpha` mass** (q side of C2, route §5.3 J1): the
normalized Haar log-mass of the actual root principal lattice `urRootAlpha·O_L` is
`(1/(2*l)) log ‖q_b‖` (Kummer `r^{2l}=q`, no hypothesis, no `rfl`, instance
aligned with the normed-algebra module). -/
theorem urRootAlpha_mass :
    (1 / (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : ℝ)) *
      (Real.log (rootExtensionHaar T b
          ((urRootAlpha T b) • (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b)))).toReal -
        Real.log (rootExtensionHaar T b
          (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b))).toReal) =
      (1 / (2 * (l.value : ℝ))) * Real.log ‖((sourceRootQUnit T b : rootBase T b))‖ := by
  have hball : (Integers (rootNormedExtension T b) : Set (rootNormedExtension T b)) =
      rootExtensionUnitBall T b := by
    rw [show (Integers (rootNormedExtension T b) : Set (rootNormedExtension T b)) =
      Metric.closedBall (0 : rootNormedExtension T b) 1 from ?_]
    · rfl
    · ext x
      change x ∈ (NormedField.valuation (K := rootNormedExtension T b)).integer ↔
        x ∈ Metric.closedBall (0 : rootNormedExtension T b) 1
      rw [mem_integers_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hmain := normalizedLogMass_kummer_root (p := qVFamTensorP T b)
    (L := rootNormedExtension T b) (rootExtensionHaar T b) (d := 2 * l.value)
    (by have := l.ge_five; omega)
    (algebraMap (rootBase T b) (rootNormedExtension T b)
      ((sourceRootQUnit T b : rootBase T b)))
    (fun h => (sourceRootQUnit T b).ne_zero
      ((algebraMap (rootBase T b) (rootNormedExtension T b)).injective (by simpa using h)))
    (urRootAlpha T b) (urRootAlpha_ne_zero T b) (urRootAlpha_pow T b)
  rw [urRootCarrier_norm_algebraMap] at hmain
  rw [hball] at hmain
  push_cast at hmain
  rw [hball]
  exact hmain

/-- **Actual per-b `urRootAlpha` mass in C1 order form**: the same mass is
`-(1/(2*l)) ord_p(q_b) log p` (the negative q term of C1). -/
theorem urRootAlpha_mass_order :
    (1 / (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : ℝ)) *
      (Real.log (rootExtensionHaar T b
          ((urRootAlpha T b) • (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b)))).toReal -
        Real.log (rootExtensionHaar T b
          (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b))).toReal) =
      -((1 / (2 * (l.value : ℝ))) *
        (localNormOrder (qVFamTensorP T b) ((sourceRootQUnit T b : rootBase T b)) *
          Real.log (qVFamTensorP T b : ℝ))) := by
  rw [urRootAlpha_mass, urRootQ_log_norm_order]
  ring

#print axioms urRootTheta_mass
#print axioms urRootTheta_mass_neg_order
#print axioms urRootQ_log_norm_order
#print axioms urRootAlpha_mass
#print axioms urRootAlpha_mass_order

end LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual
end