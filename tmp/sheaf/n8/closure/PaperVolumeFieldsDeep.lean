import tmp.sheaf.n8.closure.PaperNormalizedVolumeActualAttempt
import tmp.sheaf.n8.closure.C7ActualFromSource
import tmp.sheaf.n8.Group6Normalization

/-! # Deep derivation of PaperNormalizationSourceData fields (write-only)

Task-530 attempt.  It separates the *formula* fields, which are derivable
from the local volume and paper normalization schemas, from the actual source
weight/procession primitives, which are not present in the tree.

## Derived fields

* `paperLocalVolumeActual` (already actual from Group6/PaperLocalVolumeData).
* `globalVolume` is *defined* from the paper formula
  `local.normalizedVolume * sum_i lambda_i`, and `globalVolume_eq` is `rfl`.
* `processionAverageValue` is *defined* from the paper formula
  `processionAverage processionWeights`, and its equation is `rfl`.
* Thus the named global-normalization identity holds by `rfl` for the
  constructed `PaperNormalizedVolumeData` once the source primitives are
  supplied.

## Exact missing primitives

* `PaperLambdaData iota`: actual paper `lambda_v` weights; not constructed.
* `PaperTupleWeightData iota`: actual tuple weights with common denominator;
  not constructed.
* `processionLength : Nat`; not determined by the actual C6 tensor tuple.
* `processionWeights : Fin processionLength -> Real`; not determined.

Theorem `paperNormalizationSourceData_nonempty_iff_primitives` proves that
`PaperNormalizationSourceData` is nonempty iff exactly these four source
primitives exist.  No arbitrary weights, constants, PUnit, True, or axiom is
used.  `paperNormalizedVolume_global_normalization` is not asserted globally;
only the constructed instance is evaluated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8C6.PaperNormalizedVolume

open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory BigOperators

universe u v w ua uv upi umon ui

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {V : iota → Type w}
variable (places : (i : iota) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

/-- Actual local volume from Group6 normalization. -/
abbrev actualLocalVolume : PaperLocalVolumeData places tuple mu :=
  PaperLocalVolumeData.actual places tuple mu

/-- The exact four source primitives missing from production. -/
structure PaperVolumePrimitives where
  lambdaData : PaperLambdaData iota
  tupleWeights : PaperTupleWeightData iota
  processionLength : Nat
  processionLength_pos : 0 < processionLength
  processionWeights : Fin processionLength -> Real

namespace PaperVolumePrimitives

variable (P : PaperVolumePrimitives (iota := iota))

/-- Paper global volume formula from the actual local volume and the source
lambda weights. -/
def globalVolume : Real :=
  (actualLocalVolume places tuple mu).normalizedVolume *
    (∑ i : iota, P.lambdaData.lambda i)

/-- Paper procession average from the source procession weights. -/
def processionAverageValue : Real :=
  processionAverage P.processionWeights

/-- Assemble the actual source normalization data. The global-volume identity
and procession-average value are definitional, not extra assumptions. -/
def toSourceData : PaperNormalizationSourceData places tuple mu where
  lambdaData := P.lambdaData
  tupleWeights := P.tupleWeights
  processionLength := P.processionLength
  processionLength_pos := P.processionLength_pos
  processionWeights := P.processionWeights
  processionAverageValue := P.processionAverageValue
  globalVolume := P.globalVolume
  globalVolume_eq := rfl

@[simp] theorem toSourceData_lambdaData :
    P.toSourceData.lambdaData = P.lambdaData := rfl

@[simp] theorem toSourceData_tupleWeights :
    P.toSourceData.tupleWeights = P.tupleWeights := rfl

@[simp] theorem toSourceData_processionLength :
    P.toSourceData.processionLength = P.processionLength := rfl

@[simp] theorem toSourceData_processionWeights :
    P.toSourceData.processionWeights = P.processionWeights := rfl

@[simp] theorem toSourceData_processionAverageValue :
    P.toSourceData.processionAverageValue = P.processionAverageValue := rfl

@[simp] theorem toSourceData_globalVolume :
    P.toSourceData.globalVolume = P.globalVolume := rfl

/-- The constructed global volume satisfies the paper normalization formula
by definition. -/
theorem toSourceData_globalVolume_eq :
    P.toSourceData.globalVolume =
      (actualLocalVolume places tuple mu).normalizedVolume *
        (∑ i : iota, P.lambdaData.lambda i) := rfl

/-- The constructed procession average is the paper mean of the source
procession weights. -/
theorem toSourceData_processionAverage_eq :
    P.toSourceData.processionAverageValue =
      processionAverage P.processionWeights := rfl

/-- The resulting PaperNormalizedVolumeData satisfies the formerly-sorry
global normalization identity for this constructed instance. -/
theorem toPaperNormalizedVolumeData_global_normalization :
    P.toSourceData.toPaperNormalizedVolumeData.globalVolume =
      P.toSourceData.toPaperNormalizedVolumeData.localVolume.normalizedVolume *
        (∑ i : iota,
          P.toSourceData.toPaperNormalizedVolumeData.lambdaData.lambda i) := rfl

end PaperVolumePrimitives

namespace PaperNormalizationSourceData

variable (S : PaperNormalizationSourceData places tuple mu)

/-- Extract the exact source primitives from an existing source-data package. -/
def toPrimitives : PaperVolumePrimitives (iota := iota) where
  lambdaData := S.lambdaData
  tupleWeights := S.tupleWeights
  processionLength := S.processionLength
  processionLength_pos := S.processionLength_pos
  processionWeights := S.processionWeights

@[simp] theorem toPrimitives_lambdaData :
    S.toPrimitives.lambdaData = S.lambdaData := rfl

@[simp] theorem toPrimitives_tupleWeights :
    S.toPrimitives.tupleWeights = S.tupleWeights := rfl

@[simp] theorem toPrimitives_processionLength :
    S.toPrimitives.processionLength = S.processionLength := rfl

@[simp] theorem toPrimitives_processionWeights :
    S.toPrimitives.processionWeights = S.processionWeights := rfl

/-- Exact nonempty equivalence: source-data package exists iff the four
paper weight/procession primitives exist.  The formula fields are derived, not
primitive. -/
theorem paperNormalizationSourceData_nonempty_iff_primitives :
    Nonempty (PaperNormalizationSourceData places tuple mu) ↔
      Nonempty (PaperVolumePrimitives (iota := iota)) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.toPrimitives⟩
  · rintro ⟨P⟩
    exact ⟨P.toSourceData⟩

end PaperNormalizationSourceData

/-- Actual C3 tensor tuple instance of the local volume (C6 actual data). -/
section C3Actual

variable {l : PrimeGeFive} {Vc : Type uv}
variable {I : LeanFormal.IUT.Theorem311Source.OriginalInput
  (l := l) (V := Vc)}
variable (C3 : LeanFormal.IUT.N8Closure.SourcePilotRegion.SourcePilotRegionData
  (I := I))

/-- The actual C3 local volume: the C3 tensor tuple plugged into the actual
Group6 local volume. -/
def c3ActualLocalVolume
    [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    (muC3 : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
    [Measure.IsAddHaarMeasure muC3] :
    PaperLocalVolumeData C3.tensorPlaces C3.tensorTuple muC3 :=
  PaperLocalVolumeData.actual C3.tensorPlaces C3.tensorTuple muC3

end C3Actual

end LeanFormal.IUT.N8C6.PaperNormalizedVolume

end
