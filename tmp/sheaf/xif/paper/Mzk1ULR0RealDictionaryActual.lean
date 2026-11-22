/- R0.1 (ROUTE ALIGNMENT 20261118, supersedes c=order): c_P = v_P(q_P)/e_P^abs.
   - order_c := ((qVFamily T b).order : R) = v_P(q_P) raw;
   - eAbs := absolute ramification index of the qVFam F-place over its rational prime;
   - cP := order_c / eAbs (route/paper c_P; spectral norm already contains absolute ramification:
     do NOT divide again by e(P/b));
   - spectral bridge (per b): spectral = cP - log(qVFamNormRatio)/log p, ratio=1 => spectral=cP.
   Legacy spectral correction stays in Mzk1ULR0ActualQCorrectionActual.
   R0.2 Qb/M_paper_v2 unchanged (raw v_P = orderAtFPlace).
   Ref: coord/ROUTE-ALIGNMENT-20261118.md §R0; IUT IV L1261-1296. -/
import tmp.sheaf.xif.paper.Mzk1ULR0ActualQCorrectionActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR0RealDictionaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- raw v_P(q_P) = q-order. -/
noncomputable def order_c (b : Bad (nativePlaceSelection T)) : Real :=
  ((qVFamily T b).order : Real)

/-- absolute ramification index e_P^abs of the qVFam F-place over its rational prime. -/
noncomputable def eAbs (b : Bad (nativePlaceSelection T)) : Real :=
  ((qVFamTensorPlace T b).maximalIdeal.asIdeal.ramificationIdx ℤ : Real)

/-- paper c_P = v_P(q_P)/e_P^abs (route §2.1). -/
noncomputable def cP (b : Bad (nativePlaceSelection T)) : Real :=
  order_c (l := l) T b / eAbs (l := l) T b

/-- Main: cP = order_c / e_abs (rfl, e = e_abs). -/
theorem cP_eq_order_div_e (b : Bad (nativePlaceSelection T)) :
    cP (l := l) T b = order_c (l := l) T b / eAbs (l := l) T b := rfl

/-- raw order is v_P(q_P) (rfl). -/
theorem order_c_eq_order (b : Bad (nativePlaceSelection T)) :
    order_c (l := l) T b = ((qVFamily T b).order : Real) := rfl

/-- Spectral bridge: given paper coefficient = cP, spectral = cP - log ratio/log p (per b). -/
theorem spectral_eq_cP_sub_normRatio (b : Bad (nativePlaceSelection T))
    (hpaper : paperNormalizedCoefficient T b = cP (l := l) T b) :
    QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
      cP (l := l) T b -
        Real.log (qVFamNormRatio T b) / Real.log (qVFamTensorP T b : Real) := by
  rw [← hpaper]
  exact c_norm_eq_paperCoefficient_sub_normRatio T b

/-- qVFamNormRatio = 1 and paper coefficient = cP => spectral = cP. -/
theorem spectral_eq_cP_of_normRatio_one (b : Bad (nativePlaceSelection T))
    (hpaper : paperNormalizedCoefficient T b = cP (l := l) T b)
    (h : qVFamNormRatio T b = 1) :
    QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
      cP (l := l) T b := by
  have hb := spectral_eq_cP_sub_normRatio (T := T) b hpaper
  rw [h, Real.log_one, zero_div, sub_zero] at hb
  exact hb

#print axioms cP_eq_order_div_e
#print axioms order_c_eq_order
#print axioms spectral_eq_cP_sub_normRatio
#print axioms spectral_eq_cP_of_normRatio_one

end LeanFormal.IUT.XiFPaper.Mzk1ULR0RealDictionaryActual
