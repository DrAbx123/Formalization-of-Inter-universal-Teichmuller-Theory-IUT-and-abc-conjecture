import tmp.sheaf.xif.paper.PaperBadPlaceTensorGeometryActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual

/-! # Paper constants on the bad-place product Theta hull

The S13/S13b per-b hull uses `rootNormCoefficient` and `rootHalfCoefficient`, i.e.
the normalized coefficient divided by 2l.  The actual paper q-variable is
`q_v^(1/(2l))`, so the j^2 theta coefficient is `j^2 * order(q_v)/(2l)`, not
`j^2 * order(q_v)`.  This file records the exact relation between the
normalized-supply coefficient and the paper root coefficient, including the
correction factor when the normalized coefficient is not definitionally the
order.  It also records the weight normalization used on the product carrier.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The actual paper root coefficient order(q_v)/(2l). -/
noncomputable def paperRootCoefficient : Real :=
  qVFamPaperRootCoefficient T b

/-- The S13 per-b half coefficient c_norm/(2l). -/
noncomputable def s13HalfCoefficient : Real :=
  rootHalfCoefficient (l := l) T b ()

/-- The exact correction denominator: the normalized-supply coefficient minus
the actual order. -/
noncomputable def normalizedOrderCorrection : Real :=
  QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b - ((qVFamily T b).order : Real)

/-- Exact relation: S13 half coefficient = paper root coefficient plus the
normalized/order correction divided by 2l. -/
theorem s13HalfCoefficient_eq_paperRootCoefficient_add_correction :
    s13HalfCoefficient T b =
      paperRootCoefficient T b +
        normalizedOrderCorrection T b / (2 * l.value : Real) := by
  unfold s13HalfCoefficient paperRootCoefficient normalizedOrderCorrection
    rootHalfCoefficient rootNormCoefficient qVFamNormalizedCoefficientFamily
    qVFamPaperRootCoefficient
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  field_simp [htwo]
  ring

/-- The S13 half coefficient is the paper root coefficient when the normalized
coefficient is the actual order. -/
theorem s13HalfCoefficient_eq_paperRootCoefficient_of_normalized_eq_order
    (h : QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
      ((qVFamily T b).order : Real)) :
    s13HalfCoefficient T b = paperRootCoefficient T b := by
  rw [s13HalfCoefficient_eq_paperRootCoefficient_add_correction]
  unfold normalizedOrderCorrection
  rw [h, sub_self, zero_div, add_zero]

/-- The j^2 coefficient used by S13: j^2 * c_norm/(2l). -/
noncomputable def s13ThetaCoefficient (j : SignedLabel l.value) : Real :=
  ((gaussExponent j.1).toNat : Real) * s13HalfCoefficient T b

/-- The actual paper theta coefficient: j^2 * order(q_v)/(2l). -/
noncomputable def paperThetaCoefficient (j : SignedLabel l.value) : Real :=
  qVFamPaperThetaTensorCoefficient T b j

/-- Exact correction formula for the S13 theta coefficient. -/
theorem s13ThetaCoefficient_eq_paper_add_correction
    (j : SignedLabel l.value) :
    s13ThetaCoefficient T b j =
      paperThetaCoefficient T b j +
        ((gaussExponent j.1).toNat : Real) *
          normalizedOrderCorrection T b / (2 * l.value : Real) := by
  unfold s13ThetaCoefficient paperThetaCoefficient qVFamPaperThetaTensorCoefficient
    qVFamPaperRootCoefficient normalizedOrderCorrection
  rw [s13HalfCoefficient_eq_paperRootCoefficient_add_correction]
  unfold paperRootCoefficient normalizedOrderCorrection qVFamPaperRootCoefficient
  ring

/-- The actual classical q^(j^2) coefficient is 2l times the paper root theta
coefficient; the hull must not use this classical coefficient directly. -/
theorem classicalThetaCoefficient_eq_twoL_mul_paper
    (j : SignedLabel l.value) :
    qVFamThetaTensorCoefficient T b j () =
      (2 * l.value : Real) * paperThetaCoefficient T b j := by
  unfold paperThetaCoefficient qVFamPaperThetaTensorCoefficient
    qVFamPaperRootCoefficient qVFamThetaTensorCoefficient
  have h := congrFun (qVFamThetaTensorCoefficient_eq_twoL_mul_rootCoefficient (l := l) T b j) ()
  simpa [paperThetaCoefficient, qVFamPaperThetaTensorCoefficient,
    qVFamPaperRootCoefficient] using h

/-- The actual 2l-th-root theta value is the j^2 power of the actual root; not
a power of the classical q_v. -/
theorem paperThetaValueRoot_is_root_power
    (j : SignedLabel l.value) :
    qVFamPaperThetaValueRoot T b j =
      (hodgeTwoLthRoot T b) ^ (gaussExponent j.1).toNat := rfl

/-- Local weight used by the product comparison, from Cor 3.12 normalization. -/
noncomputable def productLocalWeight : Real :=
  nativeBadLocalWeight T b

/-- The product comparison uses exactly the inverse completion-degree local
weight; it does not introduce a second label weight. -/
theorem productLocalWeight_eq_inv_degree :
    productLocalWeight T b =
      ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Nat) : Real)⁻¹ :=
  nativeBadLocalWeight_eq_inv T b

/-- If a procession average normalization is applied, its exact factor is the
uniform label weight 1/(l-1), separate from the local weight. -/
noncomputable def productProcessionFactor : Real :=
  processionLabelWeight l

theorem productProcessionFactor_eq_inv_card :
    productProcessionFactor (l := l) =
      (Fintype.card (ProcessionLabel l) : Real)⁻¹ := rfl


/-- The procession label factor is nonnegative. -/
theorem productProcessionFactor_nonneg :
    0 ≤ productProcessionFactor (l := l) := by
  unfold productProcessionFactor
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Applying the Cor 3.12 procession-average factor to the S13 weighted
comparison multiplies both sides by the same nonnegative factor. -/
theorem productProcession_scaled_comparison
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : Bad (nativePlaceSelection T)) →
      Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)] :
    productProcessionFactor (l := l) *
        badPlaceWeightedProductQPilotSignedLog T μ ≤
      productProcessionFactor (l := l) *
        badPlaceWeightedThetaHullMuLog T μ :=
  mul_le_mul_of_nonneg_left
    (badPlaceWeightedQPilot_le_weightedThetaHull T μ)
    (productProcessionFactor_nonneg (l := l))

/-- Procession weights sum to one over the actual label group F_l^x. -/
theorem productProcessionFactor_total :
    (∑ _j : ProcessionLabel l, productProcessionFactor (l := l)) = 1 := by
  unfold productProcessionFactor
  exact processionLabelWeight_total l


end LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
