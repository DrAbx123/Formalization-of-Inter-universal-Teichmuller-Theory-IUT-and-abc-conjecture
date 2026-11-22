import tmp.sheaf.xif.paper.Mzk1GapDetHaarAssemblyActual
import tmp.sheaf.xif.paper.Mzk1DetHaarDegreeFactorActual
import Mathlib.MeasureTheory.Measure.Haar.Unique
/-! GAP-DET-HAAR degree factor identification -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarDegreeIdentificationActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetHaarProofActual
open LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarSNFSplitActual
open LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1DetHaarDegreeFactorActual
variable {E : Type*} [MeasurableSpace E]
/-- Degree factor scaling from explicit factors: c = ofReal ‖detB‖. -/
theorem detHaar_degree_scaling_of_factors
    (B U D W : E -> E) (hB : B = U ∘ D ∘ W)
    (hUmeas : Measurable U) (hDmeas : Measurable D) (hWmeas : Measurable W)
    (μ : Measure E) (hU : μ.map U = μ) (hW : μ.map W = μ)
    (Df : DetHaarDegreeFactor)
    (hD : μ.map D = Df.c • μ) :
    μ.map B = Df.c • μ :=
  detHaar_map_of_factors B U D W hB hUmeas hDmeas hWmeas μ hU hW Df.c hD
/-- The identified scaling is exactly the ENNReal of the real determinant norm. -/
theorem detHaar_degree_scaling_eq_ofReal
    (B U D W : E -> E) (hB : B = U ∘ D ∘ W)
    (hUmeas : Measurable U) (hDmeas : Measurable D) (hWmeas : Measurable W)
    (μ : Measure E) (hU : μ.map U = μ) (hW : μ.map W = μ)
    (Df : DetHaarDegreeFactor)
    (hD : μ.map D = Df.c • μ) :
    μ.map B = ENNReal.ofReal ‖Df.detB‖ • μ :=
  (detHaar_degree_scaling_of_factors B U D W hB hUmeas hDmeas hWmeas μ hU hW Df hD).trans
    (by rw [Df.c_eq, Real.norm_eq_abs])
/-- Exact missing identification: diagonal SNF factor D realizes the ENNReal
of the real determinant norm. -/
def detHaarDegreeIdentificationMissing : List String :=
  [ "diagonal SNF factor D has μ.map D = ofReal ‖detB‖ • μ",
    "real determinant norm of the SNF diagonal equals product p^{-e}" ]
theorem detHaarDegreeIdentificationMissing_length :
    detHaarDegreeIdentificationMissing.length = 2 := rfl
#check detHaar_degree_scaling_of_factors
#check detHaar_degree_scaling_eq_ofReal
end LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarDegreeIdentificationActual
end
