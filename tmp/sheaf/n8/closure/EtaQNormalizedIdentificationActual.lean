import tmp.sheaf.n8.closure.EtaComparisonConsumer
import tmp.sheaf.n8.closure.EtaFPlaceComparisonProof

/-!
# EtaQNormalizedIdentificationActual

Actual proof of the normalized identification `O.Q = EtaNativeQ X` for the
paper C9 output, using the production `PaperC9Output.Q_eq_nativeScalar`.

The actual F-place q scalar is `fPlaceNormalizedQVolume X`; production proves
it equals `qPilotSignedLog X = EtaNativeQ X`.  The F-place *shell logVolume*
normalization is a different, false target: its sign is nonnegative while the
normalized q volume is negative.  That sign boundary is recorded, not assumed.

No free identification and no common Real line are introduced.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.PaperQLeThetaReduction
open LeanFormal.IUT.N8Closure.EtaRouteInterface
open LeanFormal.IUT.N8Closure.EtaComparisonConsumer
open LeanFormal.IUT.N8Closure.EtaFPlaceComparisonProof
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison

namespace LeanFormal.IUT.N8Closure.EtaQNormalizedIdentificationActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Actual normalized identification: the paper C9 Q is the native q scalar. -/
theorem etaQNormalizedIdentification_actual
    (O : PaperC9Output (X := X) mu) :
    EtaQNormalizedIdentification (X := X) O := by
  unfold EtaQNormalizedIdentification EtaNativeQ
  exact C9PaperClosure.PaperC9Output.Q_eq_nativeScalar O

/-- The actual F-place normalized q volume is the native q scalar. -/
theorem etaNativeQ_eq_fPlaceNormalizedQVolume :
    EtaNativeQ X = fPlaceNormalizedQVolume X := by
  rw [EtaNativeQ, fPlaceNormalizedQVolume_eq_signedLog]

/-- The paper Q equals the actual F-place normalized q volume. -/
theorem paperQ_eq_fPlaceNormalizedQVolume
    (O : PaperC9Output (X := X) mu) :
    O.Q = fPlaceNormalizedQVolume X := by
  rw [etaQNormalizedIdentification_actual (X := X) (mu := mu) O,
    etaNativeQ_eq_fPlaceNormalizedQVolume]

/-- Exact normalization boundary: the F-place shell logVolume target is false
(nonnegative shell volume versus negative normalized q volume). -/
theorem fPlaceShellNormalization_false :
    ¬ EtaFPlaceNormalizedComparisonTarget X :=
  etaFPlaceNormalizedComparisonTarget_false X

/-- Actual normalized identification package for the paper C9 output, with the
F-place q scalar and the exact shell-volume obstruction. -/
structure EtaQNormalizedIdentificationData
    (O : PaperC9Output (X := X) mu) where
  paper_eq_nativeQ : O.Q = EtaNativeQ X
  nativeQ_eq_fPlace : EtaNativeQ X = fPlaceNormalizedQVolume X
  paper_eq_fPlace : O.Q = fPlaceNormalizedQVolume X
  shellTarget_false : ¬ EtaFPlaceNormalizedComparisonTarget X

noncomputable def etaQNormalizedIdentificationData
    (O : PaperC9Output (X := X) mu) :
    EtaQNormalizedIdentificationData (X := X) (mu := mu) O where
  paper_eq_nativeQ := etaQNormalizedIdentification_actual (X := X) (mu := mu) O
  nativeQ_eq_fPlace := etaNativeQ_eq_fPlaceNormalizedQVolume X
  paper_eq_fPlace := paperQ_eq_fPlaceNormalizedQVolume (X := X) (mu := mu) O
  shellTarget_false := fPlaceShellNormalization_false X

theorem etaQNormalizedIdentificationData_nonempty
    (O : PaperC9Output (X := X) mu) :
    Nonempty (EtaQNormalizedIdentificationData (X := X) (mu := mu) O) :=
  ⟨etaQNormalizedIdentificationData (X := X) (mu := mu) O⟩

end LeanFormal.IUT.N8Closure.EtaQNormalizedIdentificationActual