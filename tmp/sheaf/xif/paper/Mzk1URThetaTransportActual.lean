/- U-R C2 theta side second half: **root-extension -> tensor transport** (task-13).

Route §5.3 J1 main line.  The missing object is a single real-number identity:

  `actualLocalHullLog T b = log ‖urRootAlpha T b‖`

i.e. the tensor-block normalized log Haar volume of the actual theta hull equals
the normalized log-mass of the root principal lattice `r_b O_L` in the actual finite
root extension `rootNormedExtension T b` (where `r_b^{2l} = q_b`).

This file is the **design/interface** deliverable (first round of task-13):

* `RootTensorVolumeAlignmentAt` : the exact transport target (a `Prop`, retained
  without inhabitant; no sorry/axiom);
* `RootTensorVolumeAlignmentWithCorrection` : the refined target allowing an explicit
  local index/different correction `Δ_b` (route §5.3: "若参考格不同，保留明确的
  index/different correction，归入 C1 已有项");
* proved here: the root-side log-norm identity `ur_alpha_log_norm_eq` and
  `thetaCoeff_eq_neg_alpha_log` (so the tensor-volume alignment *implies* the
  root-hull scaling formula and hence `htheta`), plus the composition
  `ur_htheta_of_alignment`.

What is still missing (documented, not faked): a proof of the alignment itself.  It
cannot be an element-level equality (the `2l`-th root `r_b` lives only in the root
extension, not in the tensor block: `S342QVFamilyRootImpossibleActual`), and the
tensor-block fractional scaling data at `c_norm/(2l)` is exactly
`RootHullHalfScalingDataGap` of `BadPlaceRootHullScalingFormulaActual` (unavailable).
The feasible remaining routes (reported to Lead) are:
(a) prove the alignment through the **different/index correction**: the tensor hull
    volume equals the root lattice log-volume up to the `L/K_b` different term
    (`localDifferentPaperOrder`, available from
    `Mzk1LpDifferentBoundActual`/`LocalDifferentUpperBound`), which is exactly the C1 different
    budget; or
(b) realize the root lattice's shadow in the tensor block via a finite quotient
    (J3), which needs source-side finite quotients not present in the tree.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaHthetaActual
import tmp.sheaf.xif.paper.Mzk1URRootExtInstancesActual
import tmp.sheaf.xif.paper.Mzk1URQNormalizationActual
import tmp.sheaf.xif.paper.Mzk1URRootExtensionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual
open LeanFormal.IUT.XiFPaper.Mzk1URQNormalizationActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHthetaActual
open LeanFormal.IUT.XiFPaper.BadPlaceThetaHullCorrectionFormulaActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]

/-- **The exact transport target** (task-13, retained without inhabitant): the
tensor-block normalized log Haar volume of the actual theta hull equals the
normalized log-mass of the actual root principal lattice `r_b O_L` in the actual
finite root extension. -/
def RootTensorVolumeAlignmentAt (b : Bad (nativePlaceSelection T)) : Prop :=
  actualLocalHullLog (l := l) T b =
    Real.log ‖(urRootAlpha T b : urRootCarrier T b)‖

/-- Refined transport target with an explicit local index/different correction
`Δ_b` (route §5.3: reference-lattice change is kept as an explicit correction
and charged to the C1 different budget). -/
def RootTensorVolumeAlignmentWithCorrection
    (b : Bad (nativePlaceSelection T)) (Delta : ℝ) : Prop :=
  actualLocalHullLog (l := l) T b + Delta =
    Real.log ‖(urRootAlpha T b : urRootCarrier T b)‖

/-- **Root-side log-norm identity**: `log ‖r_b‖ = (1/(2l)) log ‖q_b‖` from the
actual Kummer relation `r_b^{2l} = q_b` (`urRootAlpha_pow`, no positivity hypothesis
needed beyond nonvanishing). -/
theorem ur_alpha_log_norm_eq
    (b : Bad (nativePlaceSelection T)) :
    Real.log ‖(urRootAlpha T b : urRootCarrier T b)‖ =
      (1 / (2 * (l.value : ℝ))) *
        Real.log ‖((sourceRootQUnit T b : rootBase T b))‖ := by
  have hnorm : ‖(urRootAlpha T b : urRootCarrier T b)‖ ^ (2 * l.value) =
      ‖((sourceRootQUnit T b : rootBase T b))‖ := by
    rw [← norm_pow, urRootAlpha_pow, urRootCarrier_norm_algebraMap]
  have hnpos : (0 : ℝ) < ‖(urRootAlpha T b : urRootCarrier T b)‖ :=
    norm_pos_iff.mpr (urRootAlpha_ne_zero T b)
  have hcast : ((2 * l.value : ℕ) : ℝ) = 2 * (l.value : ℝ) := by push_cast; ring
  have hpos2 : (0 : ℝ) < 2 * (l.value : ℝ) := by
    have := l.ge_five; positivity
  have h := congrArg Real.log hnorm
  rw [Real.log_pow] at h
  rw [hcast] at h
  rw [← h]
  field_simp [hpos2.ne']
  have hl0 : (l.value : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := l.ge_five; omega)
  field_simp [hl0]

/-- The root-hull coefficient is minus the root-side log-norm:
`-thetaCoefficientContribution = log ‖r_b‖`. -/
theorem thetaCoeff_eq_neg_alpha_log
    (b : Bad (nativePlaceSelection T)) :
    -thetaCoefficientContribution (l := l) T b =
      Real.log ‖(urRootAlpha T b : urRootCarrier T b)‖ := by
  have hlogp : Real.log (qVFamTensorP T b : ℝ) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt)).ne'
  have hl : (2 * (l.value : ℝ)) ≠ 0 := by
    have := l.ge_five; positivity
  have hlog := urRootQ_log_norm_order (T := T) (b := b)
  have hc : qVFamNormalizedCoefficient T b =
      localNormOrder (qVFamTensorP T b) ((sourceRootQUnit T b : rootBase T b)) := by
    rw [ur_cNorm_eq_localNormOrder, ur_gen_eq_sourceRootQUnit]
    rfl
  unfold thetaCoefficientContribution
  rw [ur_alpha_log_norm_eq, hc, hlog]
  ring

/-- **Alignment implies the root-hull scaling formula** (hence `htheta`). -/
theorem rootHullScalingFormulaAt_of_alignment
    (b : Bad (nativePlaceSelection T))
    (halign : RootTensorVolumeAlignmentAt (l := l) T b) :
    RootHullScalingFormulaAt (l := l) T b := by
  unfold RootHullScalingFormulaAt RootTensorVolumeAlignmentAt at *
  rw [halign, thetaCoeff_eq_neg_alpha_log]

/-- **`htheta` from the transport alignment**: the remaining U-C input reduces to the
single real-number transport target plus the per-b packet numerical comparison. -/
theorem ur_htheta_of_alignment
    (halign : ∀ b : Bad (nativePlaceSelection T),
      RootTensorVolumeAlignmentAt (l := l) T b)
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hpacket : ∀ b, -thetaCoefficientContribution (l := l) T b ≤ packetV b) :
    actualThetaHullLogRoot (l := l) T ≤
      LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
        (nativeBadLocalWeight T) packetV :=
  ur_htheta_of_scaling (l := l) T
    (fun b => rootHullScalingFormulaAt_of_alignment (l := l) T b (halign b))
    packetV hpacket

#print axioms ur_alpha_log_norm_eq
#print axioms thetaCoeff_eq_neg_alpha_log
#print axioms rootHullScalingFormulaAt_of_alignment
#print axioms ur_htheta_of_alignment

end LeanFormal.IUT.XiFPaper.Mzk1URThetaTransportActual
end