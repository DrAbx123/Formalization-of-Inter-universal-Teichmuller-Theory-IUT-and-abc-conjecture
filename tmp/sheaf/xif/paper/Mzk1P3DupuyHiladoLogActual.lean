import tmp.sheaf.xif.paper.Mzk1P3ProductHaarPiActual
/-! P3: Dupuy-Hilado normalized log `E(log mu / dim)` on the product carrier. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3DupuyHiladoLogActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1P3ProductHaarPiActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Dimension-normalized local log. -/
def normLogPerDim (logMass : ℝ) (dim : ℕ) : ℝ := logMass / dim
/-- Product normalized log divided by the total dimension is the dimension-weighted
sum of local normalized logs. -/
theorem productNormalizedLogPerDim
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b))
    (hS : ∀ b, rootExtensionHaar T b (S b) ≠ 0)
    (hSfin : ∀ b, rootExtensionHaar T b (S b) ≠ ⊤)
    (hU : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hUfin : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤)
    (D : ℝ) (hD : D ≠ 0) :
    (1 / D) * rootExtensionProductNormalizedLog T (Set.pi Set.univ S) =
      ∑ b : Bad (nativePlaceSelection T),
        (1 / D) *
          (Real.log (rootExtensionHaar T b (S b)).toReal -
            Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) := by
  rw [productNormalizedLog_pi T S hS hSfin hU hUfin, Finset.mul_sum]
/-- Dimension-weighted form: local terms divided by their own dimensions. -/
theorem productNormalizedLogPerDim_weighted
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b))
    (hS : ∀ b, rootExtensionHaar T b (S b) ≠ 0)
    (hSfin : ∀ b, rootExtensionHaar T b (S b) ≠ ⊤)
    (hU : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hUfin : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤)
    (dim : Bad (nativePlaceSelection T) → ℕ) (hdim : ∀ b, dim b ≠ 0)
    (D : ℝ) (hD : D ≠ 0) (hDsum : D = ∑ b, (dim b : ℝ)) :
    (1 / D) * rootExtensionProductNormalizedLog T (Set.pi Set.univ S) =
      ∑ b : Bad (nativePlaceSelection T),
        ((dim b : ℝ) / D) *
          normLogPerDim
            (Real.log (rootExtensionHaar T b (S b)).toReal -
              Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)
            (dim b) := by
  rw [productNormalizedLogPerDim T S hS hSfin hU hUfin D hD]
  apply Finset.sum_congr rfl
  intro b _
  unfold normLogPerDim
  field_simp [Nat.cast_ne_zero.mpr (hdim b)]
end LeanFormal.IUT.XiFPaper.Mzk1P3DupuyHiladoLogActual
end