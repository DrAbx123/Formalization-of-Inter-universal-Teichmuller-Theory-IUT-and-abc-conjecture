import tmp.sheaf.xif.paper.BadPlacePaperConstantsActual
import tmp.sheaf.xif.paper.ProcessionThetaPacketAverageActual
/-! # S642: root-normalized paper theta procession
Value uses paperThetaCoefficient (j^2 * c_norm/(2l)) and the local q log,
not realThetaValue q^(j^2) and no new rpow.  The root value identity comes
from qVFamPaperThetaValueRoot. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S642PaperRootThetaProcessionActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Uniform paper label weight 1/card. -/
noncomputable def paperRootThetaWeight : Real :=
  (c3ThetaCard (l := l) : Real)⁻¹
/-- Per-label root-normalized paper theta log value. -/
noncomputable def paperRootThetaValue (j : SignedLabel l.value) : Real :=
  -paperThetaCoefficient (l := l) T b j * Real.log (qVFamTensorP T b : Real)
/-- Root-normalized paper theta procession. -/
noncomputable def paperRootThetaProcession :
    WeightedValues (SignedLabel l.value) where
  value := paperRootThetaValue T b
  weight _ := paperRootThetaWeight (l := l)
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hcard : (c3ThetaCard (l := l) : Real) ≠ 0 := by
      exact_mod_cast (ne_of_gt (c3ThetaCard_pos (l := l)))
    exact (mul_inv_cancel₀ hcard).symm
@[simp] theorem paperRootThetaProcession_value
    (j : SignedLabel l.value) :
    (paperRootThetaProcession (l := l) T b).value j =
      paperRootThetaValue T b j := rfl
@[simp] theorem paperRootThetaProcession_weight
    (j : SignedLabel l.value) :
    (paperRootThetaProcession (l := l) T b).weight j =
      paperRootThetaWeight (l := l) := rfl
/-- Average is the uniform mean of the paper root theta values. -/
theorem paperRootThetaProcession_average :
    (paperRootThetaProcession (l := l) T b).average =
      (∑ j : SignedLabel l.value, paperRootThetaValue T b j) /
        (c3ThetaCard (l := l) : Real) := by
  unfold WeightedValues.average paperRootThetaProcession
  simp only
  rw [Finset.sum_mul]
  congr 1
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcard : (c3ThetaCard (l := l) : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt (c3ThetaCard_pos (l := l)))
  field_simp [hcard]
/-- Paper root value is the actual root power, not classical q^(j^2). -/
theorem paperRootThetaValue_root_power (j : SignedLabel l.value) :
    qVFamPaperThetaValueRoot (l := l) T b j =
      (hodgeTwoLthRoot (l := l) T b) ^ (gaussExponent j.1).toNat :=
  paperThetaValueRoot_is_root_power (l := l) T b j
/-- The classical q^(j^2) coefficient is 2l times the paper root coefficient. -/
theorem paperRootThetaCoefficient_twoL_relation
    (j : SignedLabel l.value) :
    qVFamThetaTensorCoefficient (l := l) T b j () =
      (2 * l.value : Real) * paperThetaCoefficient (l := l) T b j :=
  classicalThetaCoefficient_eq_twoL_mul_paper (l := l) T b j
end LeanFormal.IUT.XiFPaper.S642PaperRootThetaProcessionActualAdapted
