import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

/-! # Stage-4 host: concrete Haar measure family on the native qVFamTensorBlock completions

Source anchors: IUT III, Prop. 3.2, (ii) (pp. 97--99) (tensor packets of local
log-shells with additive Haar); IUT III, Remark 3.9.4 (normalization);
IUT II, Remark 2.5.1, (i).

CONSUMER: hull's S3131Stage2ModelMapGlobal (paper-route Theta side) takes
  [(b : Bad (nativePlaceSelection T)) → MeasurableSpace (qVFamTensorBlock T b)]
  and (b) → Measure (qVFamTensorBlock T b)
as INPUTS.  This file supplies them concretely:
* the actual measurable/Borel/proper topology instances on the native one-factor
  tensor block qVFamTensorBlock (product of the actual common-prime completions);
* lgpNativeHaarFamily : (b) → Measure (qVFamTensorBlock T b) := additive Haar;
* the instance (b) → Measure.IsAddHaarMeasure (lgpNativeHaarFamily T b).

Normalization is FREE for the canonical rooted readout:
arithmeticTupleNormalizedLogVolume is invariant under mu |-> c * mu because the
log(c) cancels (hull's normalization closure), so any additive Haar family works;
no unit-region mass condition or chosen constant is imposed here.

LABEL: prerequisite component (Frobenioid/mod-side data), NOT a paper object.
Registry frozen; no edits outside new files. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Borel measurable structure on the native one-factor tensor block (product
of the actual common-prime completions). -/
instance lgpNativeTensorMeasurableSpace (b : Bad (nativePlaceSelection T)) :
    MeasurableSpace (qVFamTensorBlock T b) := borel _

/-- The Borel structure is compatible with the topology. -/
instance lgpNativeTensorBorelSpace (b : Bad (nativePlaceSelection T)) :
    BorelSpace (qVFamTensorBlock T b) := ⟨rfl⟩

/-- The native tensor block is a proper space (product of complete local fields). -/
instance lgpNativeTensorProperSpace (b : Bad (nativePlaceSelection T)) :
    ProperSpace (qVFamTensorBlock T b) := inferInstance

/-- The native tensor block is locally compact. -/
instance lgpNativeTensorLocallyCompactSpace (b : Bad (nativePlaceSelection T)) :
    LocallyCompactSpace (qVFamTensorBlock T b) := inferInstance

/-- The dependent measurable-space family expected by S3131Stage2ModelMapGlobal. -/
instance lgpNativeTensorMeasurableSpacePi :
    (b : Bad (nativePlaceSelection T)) → MeasurableSpace (qVFamTensorBlock T b) :=
  fun b => lgpNativeTensorMeasurableSpace T b

/-- The dependent Borel-space family expected by S3131Stage2ModelMapGlobal. -/
instance lgpNativeTensorBorelSpacePi :
    ∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b) :=
  fun b => lgpNativeTensorBorelSpace T b

/-- The concrete additive Haar measure family on the native qVFamTensorBlock
completions. -/
noncomputable def lgpNativeHaarFamily :
    (b : Bad (nativePlaceSelection T)) → Measure (qVFamTensorBlock T b) :=
  fun _ => Measure.addHaar

/-- Each member of the family is the additive Haar measure. -/
theorem lgpNativeHaarFamily_apply (b : Bad (nativePlaceSelection T)) :
    lgpNativeHaarFamily T b = Measure.addHaar := rfl

/-- Each member of the family is an additive Haar measure (instance form). -/
instance lgpNativeHaarFamily_isAddHaar :
    (b : Bad (nativePlaceSelection T)) →
      Measure.IsAddHaarMeasure (lgpNativeHaarFamily T b) :=
  fun _ => by unfold lgpNativeHaarFamily; infer_instance

/-- Per-place form of the additive-Haar property. -/
theorem lgpNativeHaarFamily_isAddHaar_apply
    (b : Bad (nativePlaceSelection T)) :
    Measure.IsAddHaarMeasure (lgpNativeHaarFamily T b) := by
  unfold lgpNativeHaarFamily
  infer_instance

#check lgpNativeHaarFamily
#check lgpNativeHaarFamily_apply
#check lgpNativeHaarFamily_isAddHaar_apply
#check lgpNativeTensorMeasurableSpace
#check lgpNativeTensorBorelSpace
#check lgpNativeTensorMeasurableSpacePi
#check lgpNativeTensorBorelSpacePi

end LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
end