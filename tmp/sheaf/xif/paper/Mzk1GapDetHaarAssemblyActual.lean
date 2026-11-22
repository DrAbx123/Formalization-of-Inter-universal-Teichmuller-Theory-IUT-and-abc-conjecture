import tmp.sheaf.xif.paper.Mzk1P2DetHaarProofActual
import tmp.sheaf.xif.paper.Mzk1GapDetHaarSNFSplitActual
import Mathlib.MeasureTheory.Measure.Haar.Unique
/-! GAP-DET-HAAR assembly: scalar composition from explicit factors -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetHaarProofActual
open LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarSNFSplitActual
variable {E : Type*} [MeasurableSpace E]
/-- Assembly of Haar scalars along explicit factors B = U o D o W. -/
theorem detHaar_map_of_factors
    (B U D W : E -> E) (hB : B = U ∘ D ∘ W)
    (hUmeas : Measurable U) (hDmeas : Measurable D) (hWmeas : Measurable W)
    (μ : Measure E)
    (hU : Measure.map U μ = μ) (hW : Measure.map W μ = μ)
    (c : ℝ≥0∞) (hD : Measure.map D μ = c • μ) :
    Measure.map B μ = c • μ := by
  rw [hB]
  have hcompDW : Measure.map (D ∘ W) μ = Measure.map D (Measure.map W μ) :=
    (Measure.map_map hDmeas hWmeas).symm
  have hDW : Measure.map (D ∘ W) μ = c • μ := by
    rw [hcompDW, hW, hD]
  have hcompUDW : Measure.map (U ∘ D ∘ W) μ =
      Measure.map U (Measure.map (D ∘ W) μ) :=
    (Measure.map_map hUmeas (hDmeas.comp hWmeas)).symm
  rw [hcompUDW, hDW, Measure.map_smul, hU]
/-- Exact missing assembly datum: explicit B = U o D o W with the three Haar
scaling facts. -/
def detHaarAssemblyMissing : List String :=
  [ "explicit SNF factor functions U, D, W for B",
    "Haar scaling facts for U, D, W",
    "identification c = norm of det B" ]
theorem detHaarAssemblyMissing_length : detHaarAssemblyMissing.length = 3 := rfl
#check detHaar_map_of_factors
end LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarAssemblyActual
end
