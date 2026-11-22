import tmp.sheaf.xif.paper.S1567AbsNormNatGeneratorActual
import tmp.sheaf.xif.paper.S1475ReportCExactInputsActual
import tmp.sheaf.xif.paper.S853OInFZeroAbsorptionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1570ReportCInputsClosedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1086PerBQ1URootHullActual
open LeanFormal.IUT.XiFPaper.S1087Q1UContainmentActual
open LeanFormal.IUT.XiFPaper.S1475ReportCExactInputsActual
open LeanFormal.IUT.XiFPaper.S1567AbsNormNatGeneratorActual
open LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual
open LeanFormal.IUT.XiFPaper.S853OInFZeroAbsorptionActual
open LeanFormal.IUT.XiFPaper.S863ProductImageCompactActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (N8Closure.nativePlaceSelection T))]
variable [∀ b : Bad (N8Closure.nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (N8Closure.nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (N8Closure.nativePlaceSelection T))

/-- S1567's actual S1087 coefficient comparison gives the actual region
containment, and S1475's injective-embedding reduction gives the q[1u]
image containment. -/
theorem s1570Q1UImageContainment_actual :
    S1086Q1UImageContainment (l := l) T b := by
  apply (s1475Q1UImageContainment_iff_region (l := l) T b).mpr
  exact s1087RegionContainment (l := l) T b
    (s1567CoeffLe_actual (l := l) T b)

/-- The product-lattice identification follows from the exact S841 pointwise
absorption input via S1475. -/
theorem s1570ProductImageEq_of_pointwiseAbsorption
    (h : S841PointwiseAbsorption (l := l) T b) :
    S863ProductImageEq (l := l) T b :=
  s1475ProductImageEq_of_pointwise_absorption (l := l) T b h

/-- The product-lattice identification follows from the exact S853 input
O_hol <= F(0), through S841 pointwise absorption. -/
theorem s1570ProductImageEq_of_OLeZero
    (h : S853HolomorphicLeFractionalZero (l := l) T b) :
    S863ProductImageEq (l := l) T b :=
  s1570ProductImageEq_of_pointwiseAbsorption (l := l) T b
    (s841PointwiseAbsorption_of_O_le_zero (l := l) T b h)

/-- Exact remaining input for the product side: O_hol <= F(0); S841
pointwise absorption is its equivalent form. -/
def S1570ProductImageEqExactInput : Prop :=
  S853OLeFractionalZeroRequired (l := l) T b

/-- S841 pointwise absorption is exactly the form consumed by S1475. -/
def S1570PointwiseAbsorptionExactInput : Prop :=
  S841PointwiseAbsorption (l := l) T b

/-- Both Report-C inputs: containment actual; product conditional on the exact
O_hol <= F(0) input. -/
theorem s1570ReportCInputs_status :
    S1086Q1UImageContainment (l := l) T b ∧
      (S1570ProductImageEqExactInput (l := l) T b →
        S863ProductImageEq (l := l) T b) := by
  refine ⟨s1570Q1UImageContainment_actual (l := l) T b, ?_⟩
  intro h
  exact s1570ProductImageEq_of_OLeZero (l := l) T b h

end LeanFormal.IUT.XiFPaper.S1570ReportCInputsClosedActual

end
