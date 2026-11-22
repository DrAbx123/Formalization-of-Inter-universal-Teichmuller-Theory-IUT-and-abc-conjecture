/- Local StepV (kurt): the local-field analogue of the StepV source family, over an arbitrary
complete normed field L.  Basic objects only: local root images, their hull, and the normalized
log volume; these are the carrier-level pieces needed for the L_w route (paper Theta in L). -/
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Pointwise
open MeasureTheory
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.LocalFieldIntegralUnits

namespace LeanFormal.IUT.XiFPaper.LocalStepVActual

variable {L : Type*} [NormedField L]

/-- The local source images: multiples of the roots r^(gauss j) of the unit ball O. -/
def localRootImages {J : Type*} (r : L) (gauss : J → ℤ) (O : Set L) : Set L :=
  ⋃ j : J, (r ^ (gauss j)) • O

/-- The local source hull: closure of the union of the root images. -/
def localRootHull {J : Type*} (r : L) (gauss : J → ℤ) (O : Set L) : Set L :=
  closure (localRootImages r gauss O)

/-- Every root image is contained in the local hull. -/
theorem localRootImages_subset_hull {J : Type*} (r : L) (gauss : J → ℤ) (O : Set L) :
    localRootImages r gauss O ⊆ localRootHull r gauss O :=
  subset_closure

/-- Monotonicity of the local hull in the reference ball. -/
theorem localRootHull_mono {J : Type*} (r : L) (gauss : J → ℤ) {O O' : Set L}
    (h : O ⊆ O') : localRootHull r gauss O ⊆ localRootHull r gauss O' := by
  apply closure_mono
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
  exact Set.mem_iUnion.mpr ⟨j, Set.smul_set_mono h hj⟩

/-- The label-one root image is the single-root region r • O. -/
theorem localRootImages_one {J : Type*} [One J] (r : L) (gauss : J → ℤ) (O : Set L)
    (h : gauss 1 = 1) : (r • O : Set L) ⊆ localRootImages r gauss O := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨1, by simpa [h] using hx⟩


/-- Normalized local log volume of a set S relative to the reference ball O. -/
def localRootLogVolume [MeasurableSpace L] (μ : Measure L) (O S : Set L) : ℝ :=
  Real.log (μ S).toReal - Real.log (μ O).toReal

/-- Monotonicity of the local log volume under set inclusion (positive, finite measures). -/
theorem localRootLogVolume_mono [MeasurableSpace L] (μ : Measure L) {O S T : Set L}
    (hST : S ⊆ T) (hS : 0 < μ S) (hT : μ T < ⊤) :
    localRootLogVolume μ O S ≤ localRootLogVolume μ O T := by
  have hle : μ S ≤ μ T := measure_mono hST
  have hSne : μ S ≠ ⊤ := ne_top_of_le_ne_top hT.ne hle
  have hSpos : 0 < (μ S).toReal := ENNReal.toReal_pos hS.ne' hSne
  have hlog : Real.log (μ S).toReal ≤ Real.log (μ T).toReal :=
    Real.log_le_log hSpos (ENNReal.toReal_mono hT.ne hle)
  unfold localRootLogVolume
  linarith

/-- The local hull bound: the source images are at most the hull in log volume. -/
theorem localRootImages_logVolume_le_hull [MeasurableSpace L] (μ : Measure L) {J : Type*}
    (r : L) (gauss : J → ℤ) (O : Set L) (hS : 0 < μ (localRootImages r gauss O))
    (hT : μ (localRootHull r gauss O) < ⊤) :
    localRootLogVolume μ O (localRootImages r gauss O) ≤
      localRootLogVolume μ O (localRootHull r gauss O) :=
  localRootLogVolume_mono μ (localRootImages_subset_hull r gauss O) hS hT


/-- Closed form of the local log volume as a log of a measure ratio. -/
theorem localRootLogVolume_eq [MeasurableSpace L] (μ : Measure L) (O S : Set L)
    (hS : 0 < μ S) (hO : 0 < μ O) (hSfin : μ S < ⊤) (hOfin : μ O < ⊤) :
    localRootLogVolume μ O S = Real.log ((μ S).toReal / (μ O).toReal) := by
  unfold localRootLogVolume
  rw [Real.log_div (ENNReal.toReal_pos hS.ne' hSfin.ne').ne'
    (ENNReal.toReal_pos hO.ne' hOfin.ne').ne']

end LeanFormal.IUT.XiFPaper.LocalStepVActual
end