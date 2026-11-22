import tmp.sheaf.xif.paper.S929RQpilotPaperSHullFinalActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual

-- S930: global weighted paper inequality from S929 per-b V(R)<=V(S).
-- Only side condition: for every b, (D b).indImage subset O.
-- No equality/scaling data.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S930GlobalWeightedPaperInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S929RQpilotPaperSHullFinalActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable (D : ∀ b : Bad (nativePlaceSelection T), PaperIndImageData (l := l) T b)

/-- Exact side condition: each Ind image is bounded in O. -/
def S930IndImageBounded
    (D : ∀ b : Bad (nativePlaceSelection T), PaperIndImageData (l := l) T b) : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    (D b).indImage ⊆ S922O T b

/-- Per-b R volume. -/
noncomputable def s930VR (b : Bad (nativePlaceSelection T)) : Real :=
  s929V_R (l := l) T b (mu b)

/-- Per-b paperSHull volume. -/
noncomputable def s930VS (b : Bad (nativePlaceSelection T)) : Real :=
  s929V_S (l := l) T b (mu b) (D b)

/-- Per-b inequality from S929. -/
theorem s930PerB
    (hD : S930IndImageBounded T D)
    (b : Bad (nativePlaceSelection T)) :
    s930VR (l := l) T mu b ≤ s930VS (l := l) T mu D b :=
  s929V_R_le_V_S (l := l) T b (mu b) (D b) (hD b)

/-- Global weighted paper inequality. -/
def PaperWeightedInequality
    (D : ∀ b : Bad (nativePlaceSelection T), PaperIndImageData (l := l) T b) : Prop :=
  weightedPaperV (l := l) T (s930VR (l := l) T mu) ≤
    weightedPaperV (l := l) T (s930VS (l := l) T mu D)

theorem paperWeightedInequality_actual
    (hD : S930IndImageBounded T D) :
    PaperWeightedInequality T mu D :=
  weightedPaperV_mono T
    (fun b => s930PerB T mu D hD b)

#check paperWeightedInequality_actual
#check S930IndImageBounded
#check PaperWeightedInequality

end LeanFormal.IUT.XiFPaper.S930GlobalWeightedPaperInequalityActual

end