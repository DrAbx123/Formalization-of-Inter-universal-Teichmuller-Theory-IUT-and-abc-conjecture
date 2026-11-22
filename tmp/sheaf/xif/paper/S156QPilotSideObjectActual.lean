import tmp.sheaf.xif.paper.S22DependentProductActual
import tmp.sheaf.xif.paper.BadPlacePaperConstantsActual

/-!
# S156: q-pilot side objects (object-first, no comparison)

This file constructs the actual q-pilot-side data:

* the actual local q-parameter family q_v = qVFamily T b;
* the actual q-pilot image point in the dependent completion product;
* the actual product Haar on that ambient product;
* the actual normalized mu_log of the product unit region;
* the classical q-pilot log sum_b weight_b * order(q_v) * log p_b;
* the actual procession label normalization factor.

No comparison inequality is stated.  The exact missing paper object is the
actual multiradial image of the q-pilot and the Haar/measure transported to that
image; that gap is recorded explicitly.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S156QPilotSideObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S22DependentProductActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual local q-parameter q_v, as a completion element. -/
noncomputable def QPilotQParameter
    (b : Bad (nativePlaceSelection T)) :
    Completion ((nativeBadLift T).lift b) :=
  (qVFamily T b).q

/-- Actual q-pilot image point: the dependent product of the q_v. -/
noncomputable def QPilotImagePoint : DependentCompletionProduct T :=
  fun b => QPilotQParameter T b

/-- Actual product Haar on the dependent q-pilot completion product. -/
noncomputable def QPilotAmbientHaar :
    Measure (DependentCompletionProduct T) :=
  dependentCompletionHaar T

/-- Actual normalized mu_log of the product unit region (ambient/product object). -/
noncomputable def QPilotUnitMuLog : Real :=
  dependentCompletionNormalizedMuLog T (dependentCompletionUnitRegion T)

/-- Actual classical q-pilot log: sum_b weight_b * ord_v(q_v) * log p_b. -/
noncomputable def QPilotClassicalLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (((qVFamily T b).order : Real) *
        Real.log (qVFamTensorP T b : Real))

/-- Actual procession label normalization factor (uniform 1/(l-1)). -/
noncomputable def QPilotProcessionFactor : Real :=
  productProcessionFactor (l := l)

/-- Actual procession-normalized classical q-pilot log. -/
noncomputable def QPilotProcessionNormalizedLog : Real :=
  QPilotProcessionFactor (l := l) * QPilotClassicalLog T

/-- The actual q-pilot-side object assembled from the above data. -/
structure QPilotSideObjectActual where
  qParameter : (b : Bad (nativePlaceSelection T)) ->
    Completion ((nativeBadLift T).lift b)
  qParameter_eq : qParameter = QPilotQParameter T
  imagePoint : DependentCompletionProduct T
  imagePoint_eq : imagePoint = QPilotImagePoint T
  ambientHaar : Measure (DependentCompletionProduct T)
  ambientHaar_eq : ambientHaar = QPilotAmbientHaar T
  unitMuLog : Real
  unitMuLog_eq : unitMuLog = QPilotUnitMuLog T
  classicalLog : Real
  classicalLog_eq : classicalLog = QPilotClassicalLog T
  processionFactor : Real
  processionFactor_eq : processionFactor = QPilotProcessionFactor (l := l)
  processionNormalizedLog : Real
  processionNormalizedLog_eq :
    processionNormalizedLog = QPilotProcessionNormalizedLog T

/-- Actual q-pilot-side object constructor. -/
noncomputable def qPilotSideObjectActual : QPilotSideObjectActual T where
  qParameter := QPilotQParameter T
  qParameter_eq := rfl
  imagePoint := QPilotImagePoint T
  imagePoint_eq := rfl
  ambientHaar := QPilotAmbientHaar T
  ambientHaar_eq := rfl
  unitMuLog := QPilotUnitMuLog T
  unitMuLog_eq := rfl
  classicalLog := QPilotClassicalLog T
  classicalLog_eq := rfl
  processionFactor := QPilotProcessionFactor (l := l)
  processionFactor_eq := rfl
  processionNormalizedLog := QPilotProcessionNormalizedLog T
  processionNormalizedLog_eq := rfl

/-- Exact missing object: actual multiradial image of the q-pilot object and the
Haar/measure transported to that image.  The ambient product Haar above is not
claimed to be the paper image Haar. -/
structure QPilotMultiradialImageHaarGap where
  imageCarrier : Type
  measurableSpace : MeasurableSpace imageCarrier
  imagePoint : imageCarrier
  imageHaar : @Measure imageCarrier measurableSpace
  imageHaar_isHaar : Prop
  imagePoint_is_qParameterImage : Prop
  imageHaar_transports_ambient : Prop

/-- The object-level gap is exactly the existence of the multiradial image with
its transported Haar, not a comparison statement. -/
def QPilotMultiradialImageHaarGapRequired : Prop :=
  Nonempty QPilotMultiradialImageHaarGap

end LeanFormal.IUT.XiFPaper.S156QPilotSideObjectActual

end
