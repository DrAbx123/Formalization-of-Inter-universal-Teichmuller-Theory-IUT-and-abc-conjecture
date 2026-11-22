import tmp.sheaf.xif.paper.W6ActualPilotMonodromyActual
import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual
import tmp.sheaf.xif.paper.S801PaperHullLogActual

/-! # S913: paper-order monodromy versus W6 c_norm monodromy

W6 uses c_norm for the qPilot coefficient and c_norm/(2l) for Theta, giving
the positive factor 1-1/(2l).  The paper qPilot is order/(2l) = c_norm/(2l),
the same coefficient as the paper Theta region, so the paper-order monodromy
vanishes.  The exact difference is the W6 monodromy itself. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S913PaperMonodromyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.W6ActualPilotMonodromyActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S801PaperHullLogActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Paper-order qPilot scalar: order/(2l), weighted. -/
noncomputable def paperQPilotScalar : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real)

/-- Paper Theta scalar: the same order/(2l) coefficient (paper q[2u] region). -/
noncomputable def paperThetaScalar : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real)

/-- Paper-order monodromy is identically zero. -/
theorem paperMonodromy_eq_zero :
    paperQPilotScalar (l := l) T - paperThetaScalar (l := l) T = 0 := by
  unfold paperQPilotScalar paperThetaScalar
  ring

/-- W6 monodromy in weighted c_norm form. -/
theorem w6Monodromy_eq :
    W6ActualPilotMonodromyActual.processionMonodromy T =
      (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
            Real.log (qVFamTensorP T b : Real)) *
        (1 - 1 / (2 * (l.value : Real))) := by
  unfold W6ActualPilotMonodromyActual.processionMonodromy
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [W6ActualPilotMonodromyActual.processionTermMonodromy_eq]

/-- Exact difference: W6 c_norm monodromy minus the paper-order monodromy. -/
theorem w6_sub_paperMonodromy :
    W6ActualPilotMonodromyActual.processionMonodromy T -
        (paperQPilotScalar (l := l) T - paperThetaScalar (l := l) T) =
      W6ActualPilotMonodromyActual.processionMonodromy T := by
  rw [paperMonodromy_eq_zero]
  ring

/-- Equivalent explicit difference. -/
theorem w6_sub_paperMonodromy_explicit :
    W6ActualPilotMonodromyActual.processionMonodromy T -
        (paperQPilotScalar (l := l) T - paperThetaScalar (l := l) T) =
      (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
            Real.log (qVFamTensorP T b : Real)) *
        (1 - 1 / (2 * (l.value : Real))) := by
  rw [w6_sub_paperMonodromy, w6Monodromy_eq]

/-- Paper-order monodromy is exactly zero, not positive. -/
theorem paperMonodromy_not_pos :
    ¬ 0 < paperQPilotScalar (l := l) T - paperThetaScalar (l := l) T := by
  rw [paperMonodromy_eq_zero]
  exact lt_irrefl 0

end LeanFormal.IUT.XiFPaper.S913PaperMonodromyActual
end
