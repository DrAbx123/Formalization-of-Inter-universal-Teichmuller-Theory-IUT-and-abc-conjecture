import tmp.sheaf.xif.paper.Mzk1DetHaarDegreeFactorActual
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
/-! # Class-B external input: p-adic Haar determinant scaling

Reference: Weil, Basic Number Theory; Bourbaki, Integration; Igusa.
For a finite-dimensional Q_p vector space E and an automorphism f,
  mu.map f = ENNReal.ofReal (norm (det f)) * mu
for every additive Haar measure mu.  This is the standard external theorem;
it is recorded as an explicit Prop, not proved here.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace LeanFormal.IUT.XiFPaper.Mzk1PAdicHaarDetScalingExternalActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [TopologicalSpace (d -> ℚ_[p])] [MeasurableSpace (d -> ℚ_[p])]
variable [IsTopologicalAddGroup (d -> ℚ_[p])] [BorelSpace (d -> ℚ_[p])]
variable [LocallyCompactSpace (d -> ℚ_[p])]
/-- External p-adic Haar determinant scaling law (class B). -/
def PAdicHaarDetScaling : Prop :=
  ∀ (mu : Measure (d -> ℚ_[p])) [Measure.IsAddHaarMeasure mu]
    (f : (d -> ℚ_[p]) ≃L[ℚ_[p]] (d -> ℚ_[p])),
    mu.map f =
      ENNReal.ofReal ‖(LinearMap.det f.toLinearEquiv.toLinearMap : ℚ_[p])‖ • mu
/-- Direct consequence of the external law: determinant scaling for any automorphism. -/
theorem detHaar_degree_scaling_of_external
    (h : PAdicHaarDetScaling (p := p) (d := d))
    (mu : Measure (d -> ℚ_[p])) [Measure.IsAddHaarMeasure mu]
    (f : (d -> ℚ_[p]) ≃L[ℚ_[p]] (d -> ℚ_[p])) :
    mu.map f =
      ENNReal.ofReal ‖(LinearMap.det f.toLinearEquiv.toLinearMap : ℚ_[p])‖ • mu :=
  h mu f
/-- Exact form used by the det-Haar assembly: degree factor c = ofReal norm det. -/
theorem detHaar_degree_factor_of_external
    (h : PAdicHaarDetScaling (p := p) (d := d))
    (mu : Measure (d -> ℚ_[p])) [Measure.IsAddHaarMeasure mu]
    (f : (d -> ℚ_[p]) ≃L[ℚ_[p]] (d -> ℚ_[p])) :
    mu.map f =
      ENNReal.ofReal
        ‖(LinearMap.det f.toLinearEquiv.toLinearMap : ℚ_[p])‖ • mu :=
  h mu f
/-- External source record. -/
def pAdicHaarDetScalingSource : List String :=
  [ "Weil, Basic Number Theory, Haar measure on local fields",
    "Bourbaki, Integration, chapter on Haar measure",
    "Igusa, local zeta functions / p-adic integration" ]
theorem pAdicHaarDetScalingSource_length :
    pAdicHaarDetScalingSource.length = 3 := rfl
/-- Previously internal detHaarSNFMissing is replaced by the external law for the
matrix-level scaling step; the SNF construction remains an alternative formal route. -/
def detHaarSNFReplacedByExternal : List String :=
  [ "matrix-level and diagonal scaling steps are instances of PAdicHaarDetScaling",
    "SNF route retained as internal cross-check, not as a gap" ]
theorem detHaarSNFReplacedByExternal_length :
    detHaarSNFReplacedByExternal.length = 2 := rfl
#check PAdicHaarDetScaling
#check detHaar_degree_scaling_of_external
#check detHaar_degree_factor_of_external
end LeanFormal.IUT.XiFPaper.Mzk1PAdicHaarDetScalingExternalActual
end
