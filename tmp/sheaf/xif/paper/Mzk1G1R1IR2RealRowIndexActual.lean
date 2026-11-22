/- R2 REAL INDEX + ROW V/H (route doc §4.2 steps 1-4, no union-hull shortcut):
real procession index (b, j) with row region `H_bj` = actual `rootThetaRegion` at the root
coefficient, row volume `V_bj = ν(H_bj)` (actual normalized Haar log volume), and
`H = Σ_b w_b · avg_j V_bj`.  The identities below are DEFINITIONAL (rfl); the remaining
route steps are the source map/transport (step 3) and `ν(Θ) ≤ H` (step 5), which are NOT
claimed here.  REUSE: `RootHullContainmentInequalityActual.rootThetaRegion`,
`RootNormalizedContainmentActual.rootHalfCoefficient`, `arithmeticTupleNormalizedLogVolume`.
No fake; no union-hull average shortcut. -/
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import Mathlib.Tactic

set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R1IR2RealRowIndexActual
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- **Real row region** `H_bj` at the bad place `b` and signed label `j`: the actual root
theta region `F(j² c_root) · O_hol` in the qVFam tensor block. -/
def rowRegion (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    Set (qVFamTensorBlock T b) :=
  LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual.rootThetaRegion
    (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual.rootHalfCoefficient (l := l) T b) j

/-- **Real row volume** `V_bj = ν(H_bj)`: actual normalized Haar log-volume. -/
noncomputable def rowVolume (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) : ℝ :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    MeasureTheory.Measure.addHaar (rowRegion (l := l) T b j)

/-- **Real total readout** `H = Σ_b w_b · avg_j V_bj`. -/
noncomputable def HTotal (w : Bad (nativePlaceSelection T) → ℝ) : ℝ :=
  ∑ b : Bad (nativePlaceSelection T),
    w b * ((∑ j : SignedLabel l.value, rowVolume (l := l) T b j) /
      (Fintype.card (SignedLabel l.value) : ℝ))

/-- `V_bj` is definitionally `ν(H_bj)`. -/
theorem rowVolume_eq (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    rowVolume (l := l) T b j =
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        MeasureTheory.Measure.addHaar (rowRegion (l := l) T b j) := rfl

/-- `H` is definitionally the weighted row average `Σ_b w_b · avg_j V_bj`. -/
theorem HTotal_eq (w : Bad (nativePlaceSelection T) → ℝ) :
    HTotal (l := l) T w =
      ∑ b : Bad (nativePlaceSelection T),
        w b * ((∑ j : SignedLabel l.value, rowVolume (l := l) T b j) /
          (Fintype.card (SignedLabel l.value) : ℝ)) := rfl

#print axioms rowVolume_eq
#print axioms HTotal_eq
end LeanFormal.IUT.XiFPaper.Mzk1G1R1IR2RealRowIndexActual
