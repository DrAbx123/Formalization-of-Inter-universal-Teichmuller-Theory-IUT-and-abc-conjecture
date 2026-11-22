import tmp.sheaf.n8.closure.PaperNormalizedVolume
import tmp.sheaf.n8.Group6Normalization

/-! # Attempt: concrete PaperNormalizedVolumeData from actual source data

This file builds the actual local volume component
PaperLocalVolumeData.actual from Group6Normalization and attempts to assemble
a concrete PaperNormalizedVolumeData.

Production supplies the actual local volume data, but it does not supply the
paper lambda weights, the tuple weights with a common denominator, the
procession length, the procession weights, or the paper global volume.  These
are kept as explicit source-field data in PaperNormalizationSourceData; no
arbitrary constants, PUnit, True, or axiom is used, and no missing field is
fabricated.

The paper global normalization theorem
paperNormalizedVolume_global_normalization remains a named source obligation
in PaperNormalizedVolume.lean.  This attempt does not prove it and does not
instantiate the missing source fields.

No other file is edited. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.N8C6.PaperNormalizedVolume

open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory BigOperators

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {V : iota → Type w}
variable (places : (i : iota) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

/-- The actual local volume component from the production Group6 normalization. -/
noncomputable def paperLocalVolumeActual :
    PaperLocalVolumeData places tuple mu :=
  PaperLocalVolumeData.actual places tuple mu

/-- The actual local volume is the production local volume. -/
theorem paperLocalVolumeActual_eq :
    paperLocalVolumeActual places tuple mu =
      PaperLocalVolumeData.actual places tuple mu := rfl

/-- The actual local L-V identity from Group6Normalization. -/
theorem paperLocalVolumeActual_local_identity :
    (paperLocalVolumeActual places tuple mu).haarLog =
      ((paperLocalVolumeActual places tuple mu).degree : Real) *
        (paperLocalVolumeActual places tuple mu).normalizedVolume +
      (paperLocalVolumeActual places tuple mu).unitReferenceLog :=
  PaperLocalVolumeData.local_identity
    (paperLocalVolumeActual places tuple mu)

/-- Exact paper source fields that production does not supply for the global
normalized volume: lambda weights, tuple weights, procession length/weights,
paper procession average, and global volume.  These are data fields, not
arbitrary constants. -/
structure PaperNormalizationSourceData
    (places : (i : iota) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : iota) → V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu] where
  lambdaData : PaperLambdaData iota
  tupleWeights : PaperTupleWeightData iota
  processionLength : Nat
  processionLength_pos : 0 < processionLength
  processionWeights : Fin processionLength → Real
  processionAverageValue : Real
  globalVolume : Real
  globalVolume_eq :
    globalVolume =
      (paperLocalVolumeActual places tuple mu).normalizedVolume *
        (∑ i : iota, lambdaData.lambda i)

namespace PaperNormalizationSourceData

variable (S : PaperNormalizationSourceData places tuple mu)

/-- Assemble the actual local volume with the supplied paper source fields into
a concrete PaperNormalizedVolumeData. -/
def toPaperNormalizedVolumeData :
    PaperNormalizedVolumeData places tuple mu where
  localVolume := paperLocalVolumeActual places tuple mu
  lambdaData := S.lambdaData
  tupleWeights := S.tupleWeights
  processionLength := S.processionLength
  processionLength_pos := S.processionLength_pos
  processionWeights := S.processionWeights
  processionAverageValue := S.processionAverageValue
  globalVolume := S.globalVolume

@[simp] theorem toPaperNormalizedVolumeData_localVolume :
    S.toPaperNormalizedVolumeData.localVolume =
      paperLocalVolumeActual places tuple mu := rfl

@[simp] theorem toPaperNormalizedVolumeData_lambdaData :
    S.toPaperNormalizedVolumeData.lambdaData = S.lambdaData := rfl

@[simp] theorem toPaperNormalizedVolumeData_tupleWeights :
    S.toPaperNormalizedVolumeData.tupleWeights = S.tupleWeights := rfl

@[simp] theorem toPaperNormalizedVolumeData_processionLength :
    S.toPaperNormalizedVolumeData.processionLength = S.processionLength := rfl

@[simp] theorem toPaperNormalizedVolumeData_processionWeights :
    S.toPaperNormalizedVolumeData.processionWeights = S.processionWeights := rfl

@[simp] theorem toPaperNormalizedVolumeData_processionAverageValue :
    S.toPaperNormalizedVolumeData.processionAverageValue =
      S.processionAverageValue := rfl

@[simp] theorem toPaperNormalizedVolumeData_globalVolume :
    S.toPaperNormalizedVolumeData.globalVolume = S.globalVolume := rfl

/-- The assembled global volume satisfies the supplied source normalization
identity. -/
theorem toPaperNormalizedVolumeData_globalVolume_eq :
    S.globalVolume =
      (paperLocalVolumeActual places tuple mu).normalizedVolume *
        (∑ i : iota, S.lambdaData.lambda i) :=
  S.globalVolume_eq

/-- Nonempty conditional assembly: an actual local volume together with the
explicit paper source fields yields a concrete PaperNormalizedVolumeData. -/
theorem nonempty_paperNormalizedVolumeData_of_source
    (S : PaperNormalizationSourceData places tuple mu) :
    Nonempty (PaperNormalizedVolumeData places tuple mu) :=
  ⟨toPaperNormalizedVolumeData (places := places) (tuple := tuple) (mu := mu) S⟩

end PaperNormalizationSourceData

/-! ## Exact missing production fields

The production declarations in Group6Normalization/PaperNormalizedVolume supply:

* PaperLocalVolumeData.actual and its local L-V identity;
* the definitions PaperLambdaData, PaperTupleWeightData, and
  processionAverage as data schemas.

They do NOT supply, for the actual source tuple and procession:

* a value of PaperLambdaData iota for the source iota/tuple;
* a value of PaperTupleWeightData iota;
* the paper procession length;
* the paper procession weights;
* the paper procession average value;
* the paper global volume;
* the paper global normalization identity
  paperNormalizedVolume_global_normalization.

These are exactly the fields of PaperNormalizationSourceData.  There is no
production theorem or source structure that fills them for the actual C3 tensor
block; therefore no unconditional concrete PaperNormalizedVolumeData is
constructed here.  No arbitrary constant, PUnit, True, axiom, or sorry is
used. -/

end LeanFormal.IUT.N8C6.PaperNormalizedVolume

end
