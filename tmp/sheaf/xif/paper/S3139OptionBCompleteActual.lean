import tmp.sheaf.xif.paper.S3133M1ConcretePrimeMatchActual
import tmp.sheaf.xif.paper.S3135TreeModelBaseUnitScalingActual
import tmp.sheaf.xif.paper.S3139ModelM1DischargeActual
import tmp.sheaf.xif.paper.S3133ExistingModelAdaptationActual
import Mathlib.Tactic

noncomputable section
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# S3139: Option-B completion — concrete M1 donor + base-unit interface fill (reuse)

Consumes the two Option-B completion assets (reuse, no re-proof):
* qpilot S3133M1ConcretePrimeMatchActual: on the concrete Gaussian donor the
  prime-level M1 match closes (S3131BadTensorPrimeMatch_concrete), with the donor
  record S3133M1ConcreteDonor carrying the exact remaining fields
  index_eq : C3.tensorIndex = Bad (...) and p_eq : C3.p = 5.
* abc S3135TreeModelBaseUnitScalingActual: the nontrivial procession-scaling
  interface S3133TreeModelBaseUnitScaling is filled UNCONDITIONALLY with
  baseUnit = -1 (genuine Q_5 unit of norm one).

The bundled SourceOptionBComplete records the in-model M1 evidence (S3139),
the base-unit scaling fill (abc), and the concrete donor record (qpilot).

**Component, not paper object.**  Frozen registry pair 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139OptionBCompleteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3133S3131PlaceIndexComparisonActual
open LeanFormal.IUT.XiFPaper.S3133M1InjectionReductionActual
open LeanFormal.IUT.XiFPaper.S3133M1ConcretePrimeMatchActual
open LeanFormal.IUT.XiFPaper.S3135TreeModelBaseUnitScalingActual
open LeanFormal.IUT.XiFPaper.S3139ModelM1DischargeActual
open LeanFormal.IUT.XiFPaper.S3133ExistingModelAdaptationActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- abc's base-unit interface fill is available unconditionally (reuse). -/
theorem s3139_baseUnitScaling_available :
    Nonempty S3133TreeModelBaseUnitScaling :=
  ⟨s3135_treeModelBaseUnitScaling⟩

/-- The filled base unit is -1 (reuse). -/
theorem s3139_baseUnitScaling_baseUnit :
    (s3135_treeModelBaseUnitScaling.baseUnit : ℚ_[5]) = -1 :=
  s3135_treeModelBaseUnitScaling_baseUnit

/-- The filled base unit is nontrivial (reuse). -/
theorem s3139_baseUnitScaling_nontrivial :
    (s3135_treeModelBaseUnitScaling.baseUnit : ℚ_[5]) ≠ 1 :=
  s3135_treeModelBaseUnitScaling_nontrivial

/-- On the concrete donor, the explicit prime hypothesis gives the prime-level
M1 match (reuse of qpilot's S3131BadTensorPrimeMatch_concrete). -/
theorem s3139_badTensorPrimeMatch_of_donor
    (D : S3133M1ConcreteDonor T C3)
    (hbad5 : ∀ b : Bad (nativePlaceSelection T),
      (completionRationalPrime b.1).val = 5) :
    S3131BadTensorPrimeMatch T C3 :=
  S3131BadTensorPrimeMatch_concrete T C3 hbad5 D.p_eq

/-- The Option-B completion bundle: the in-model M1 evidence (S3139), the abc
base-unit scaling fill, and the qpilot concrete donor record. -/
structure SourceOptionBComplete where
  /-- in-model M1 evidence (S3139ModelM1DischargeActual) -/
  modelM1 : Prop
  /-- abc's filled nontrivial procession-scaling datum -/
  baseUnitScaling : S3133TreeModelBaseUnitScaling
  /-- qpilot's concrete donor record (index_eq/p_eq are its exact fields) -/
  donor : S3133M1ConcreteDonor T C3

/-- The Option-B bundle is constructible from an explicit concrete donor record
(the in-model M1 evidence and base-unit fill are unconditional; the donor record
is the explicit residual input). -/
def sourceOptionBComplete (D : S3133M1ConcreteDonor T C3) :
    SourceOptionBComplete T C3 where
  modelM1 := sourceModelM1Evidence
  baseUnitScaling := s3135_treeModelBaseUnitScaling
  donor := D

/-- The Option-B bundle's model-M1 slot is inhabited in-model. -/
theorem sourceOptionBComplete_modelM1 (D : S3133M1ConcreteDonor T C3) :
    (sourceOptionBComplete T C3 D).modelM1 :=
  sourceModelM1Evidence_holds

end LeanFormal.IUT.XiFPaper.S3139OptionBCompleteActual

end
