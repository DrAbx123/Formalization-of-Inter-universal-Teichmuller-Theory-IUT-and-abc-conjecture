import tmp.sheaf.xif.paper.S3133S3131PlaceIndexComparisonActual

/-!
# Bad-only to C3 tensor-index map data (component, not a paper object)

COMPONENT, not a paper object.  Named future consumer: hull's all-place
PrimeStripC3PlaceComparison compatibility theorem (S3132*), and mainline Stage-2
model map field M1 of S3131Stage2ModelMapActual (same-C model map).

Source: IUT III, Definition 3.8, (i), p. 112-113 (q-pilot object determined by
the q_v, v in V_bad); Remark 3.1.1, (ii), p. 95-97 (completion-degree
normalization data).

The bad-only comparison has actual native provenance (nativeBadToFPlace /
nativeBadToKPlace in VbadPlaceIndexingActual) and is therefore paper-faithful;
the all-place record is trivialized without extra place provenance (hull's
S3132 result).  This file bundles the exact bad-only map data hull asked for:

* indexEquiv: the bijection Bad (nativePlaceSelection T) ≃ C3.tensorIndex;
* basePlaceProvenance: the same-C base-place identification
  (completionRationalPrime b.1).val = C3.p for every bad place b;
* the induced actual prime-level match (proved, not a field).

No index equivalence is assumed; the structure is a named Missing component and
is not inhabited here.  No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133S3131BadToC3TensorMapActual

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

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Exact named bad-only map data: the bijection of the bad places with the
Stage-2 C3 tensor index, together with the same-C base-place provenance that
forces the actual prime-level match. -/
structure S3131BadToC3TensorMapData where
  /-- bijection of the native bad places with the Stage-2 tensor index -/
  indexEquiv : Bad (nativePlaceSelection T) ≃ C3.tensorIndex
  /-- same-C base-place provenance: the bad base place has the C3 prime -/
  basePlaceProvenance : ∀ b : Bad (nativePlaceSelection T),
    (completionRationalPrime b.1).val = C3.p

/-- The bad-only map data induces the actual prime-level match (proved from the
unconditional prime comparison qVFamTensorP_eq_base_val). -/
theorem S3131BadToC3TensorMapData_primeMatch
    (D : S3131BadToC3TensorMapData T C3) :
    S3131BadTensorPrimeMatch T C3 :=
  S3131BadTensorPrimeMatch_of_basePlace T C3 D.basePlaceProvenance

/-- The indexEquiv component of the map data yields the M1 comparison Prop. -/
theorem S3131BadToC3TensorMapData_indexEquivalence
    (D : S3131BadToC3TensorMapData T C3) :
    S3131BadTensorIndexEquivalence T C3 :=
  ⟨D.indexEquiv⟩

/-- Exact structure-level Missing Prop for the bad-only map data (not
inhabited). -/
def S3131BadToC3TensorMapDataData : Prop :=
  Nonempty (S3131BadToC3TensorMapData T C3)

/-- The per-index tensorPlace match under the arithmetic-model place transport
(hull's compatibility consumer shape): bundled form of
S3131BadTensorPlaceMatch. -/
def S3131BadToC3TensorPlaceMapData
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod) : Prop :=
  S3131BadTensorPlaceMatch T C3 e placeTransport

end LeanFormal.IUT.XiFPaper.S3133S3131BadToC3TensorMapActual
