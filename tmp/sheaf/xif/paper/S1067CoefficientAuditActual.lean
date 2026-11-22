import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual

/-! # S1067: coefficient/object audit

`qPilotClassicalRegion cNorm` is F(cNorm)*O.  In the paper instance its
coefficient is `rootNormCoefficient`, definitionally the normalized-generator
supply coefficient (Supply c_norm).  Separately the module
`QVFamNormalizedCoefficientActual` proves its own normalized coefficient is
the qVFamily order (rfl).  The paper root Theta coefficient is
`paperRootCoefficientFamily = order/(2l)`.  Thus the two regions are not the
same object; any identification of Supply c_norm with order is an exact gap
(`QVFamNormalizedCoefficientGap`). -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1067CoefficientAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The QVFamNormalizedCoefficientActual coefficient is the order, rfl. -/
theorem s1067_normalizedCoefficientActual_eq_order :
    QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient T b =
      ((qVFamily T b).order : Real) := rfl

/-- The paper qPilot classical region coefficient is the supply c_norm. -/
theorem s1067_rootNormCoefficient_eq_supply (i : qVFamTensorV) :
    RootNormalizedContainmentActual.rootNormCoefficient T b i =
      QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficientFamily T b i :=
  rfl

/-- The paper root Theta coefficient is order/(2l), rfl. -/
theorem s1067_paperRootCoefficient_eq_order_div (i : qVFamTensorV) :
    paperRootCoefficientFamily T b i =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := rfl

/-- In particular the paper root coefficient is not the full order. -/
theorem s1067_paperRootCoefficient_ne_order
    (hord : 0 < ((qVFamily T b).order : Real)) :
    paperRootCoefficientFamily T b () ≠
      ((qVFamily T b).order : Real) := by
  intro h
  have hcoeff : paperRootCoefficientFamily T b () =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := rfl
  rw [hcoeff] at h
  have hlt : ((qVFamily T b).order : Real) / (2 * (l.value : Real)) <
      ((qVFamily T b).order : Real) := by
    have h5 : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
    have hl2 : (0 : Real) < 2 * (l.value : Real) := by linarith
    rw [div_lt_iff₀ hl2]
    nlinarith
  exact (ne_of_lt hlt) h

/-- Exact audit object distinction: the qPilot classical coefficient family
is the supply c_norm, while the paper root Theta coefficient family is
order/(2l). -/
def S1067CoefficientObjectsDiffer : Prop :=
  (∀ i, RootNormalizedContainmentActual.rootNormCoefficient T b i =
    QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficientFamily T b i) ∧
  (∀ i, paperRootCoefficientFamily T b i =
    ((qVFamily T b).order : Real) / (2 * (l.value : Real)))

theorem s1067CoefficientObjectsDiffer_actual :
    S1067CoefficientObjectsDiffer (l := l) T b :=
  ⟨fun i => s1067_rootNormCoefficient_eq_supply (l := l) T b i,
    fun i => s1067_paperRootCoefficient_eq_order_div (l := l) T b i⟩

/-- Exact gap if one wants the supply c_norm to equal the order. -/
def S1067SupplyCoefficientEqualsOrder : Prop :=
  QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
    ((qVFamily T b).order : Real)

end LeanFormal.IUT.XiFPaper.S1067CoefficientAuditActual
end
