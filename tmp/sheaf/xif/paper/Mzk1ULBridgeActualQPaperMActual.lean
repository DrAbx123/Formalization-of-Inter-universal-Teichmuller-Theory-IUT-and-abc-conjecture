/- q-side bridge: actualQPilotMagnitudeClassical = 2*l*M_paper_v2（逐 b 条件版，真推导）。
   actualQ term_b = nativeBadLocalWeight_b * (qVFamNormalizedCoefficient_b * log p_b);
   M_paper_v2 = Sum_b MpaperB_b（DONE Mzk1ULOrdFiberTowerActual.M_paper_v2_eq_sum_MpaperB）;
   ⇒ 若逐 b: term_b = 2*l*MpaperB_b，则全等式成立（sum_congr + mul_sum）。
   逐 b 恒等式本身是待证义务 (obligation: actualQ_paper_weight_transfer):
     nativeBadLocalWeight_b * c_norm_b * log p_b = 2*l*MpaperB_b
   ⇔ (1/[K_b:Q_p]) * order(qVFamily b) = (1/[F:Q]) * Sum_{P|b} f_P * orderAtFPlace P。
   donor: Mzk1ULQbVecActual/Mzk1ULOrdFiberTowerActual（DONE）; qVFamNormalizedCoefficient_eq_order（DONE）。 -/
import tmp.sheaf.xif.paper.Mzk1ULOrdFiberTowerActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULBridgeActualQPaperMActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1ULOrdFiberTowerActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- actualQ 的逐 b 项。 -/
noncomputable def actualQTerm (b : Bad (nativePlaceSelection T)) : Real :=
  nativeBadLocalWeight T b *
    (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
      Real.log (qVFamTensorP T b : Real))

/-- 逐 b 恒等（具名义务 actualQ_paper_weight_transfer）⇒ 全等式。 -/
theorem actualQ_eq_two_l_MpaperV2_of_per_b
    (hper : ∀ b : Bad (nativePlaceSelection T),
      actualQTerm (l := l) T b = 2 * (l.value : Real) * MpaperB (l := l) T b) :
    actualQPilotMagnitudeClassical (l := l) T =
      2 * (l.value : Real) * M_paper_v2 (l := l) T := by
  unfold actualQPilotMagnitudeClassical
  rw [M_paper_v2_eq_sum_MpaperB (l := l), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact hper b

/- REMOVED (2026-11-18): the former auxiliary lemma actualQTerm_eq_inv_degree_mul_order
claimed actualQTerm b = (1/[K_b:Q_p]) * order(qVFamily b) * log p_b, but actualQTerm uses
the SPECTRAL coefficient QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient
(exponent*degree - normRatio correction), which equals the raw order only when
qVFamNormRatio = 1 (S121). The lemma was therefore FALSE as stated; a correct replacement
must use QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient (the order coefficient)
or carry the norm-ratio bridge as a hypothesis. Kept as documented TODO for R0/R1 spectral. -/

#print axioms actualQ_eq_two_l_MpaperV2_of_per_b

end LeanFormal.IUT.XiFPaper.Mzk1ULBridgeActualQPaperMActual
