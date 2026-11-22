import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual

/-! # Mzk1Stage4CorrectedRegionB2SupportActual (stage4 lane; B2 normalization support)

A668 module: the B2 blocker of the corrected-region log law — the NORMALIZATION SPLIT
`s1902NormalizedHaar = s1902HaarScale • rootExtensionProductHaar` unwrapped to the
explicit log form of `s1902LogVolume` (in ENNReal, avoiding `ofReal`-truncation):
`s1902LogVolume T S = ofReal (log (s1902HaarScale T).toReal + log (rootExtensionProductHaar T S).toReal)`
for finite nonzero `rootExtensionProductHaar T S`.  Mainline/s1902 file is READ only.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4CorrectedRegionB2SupportActual

open MeasureTheory
open scoped ENNReal
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- B2 (measure level): the normalized Haar of a set is the scale times the product
Haar. -/
theorem s1902NormalizedHaar_apply (S : Set (S1902Carrier T)) :
    s1902NormalizedHaar T S = s1902HaarScale T * rootExtensionProductHaar T S := by
  unfold s1902NormalizedHaar
  rw [Measure.smul_apply, smul_eq_mul]

/-- B2 (log level): the normalized log-volume of a finite nonzero region is the
log of the scale plus the log of the product Haar, in exact ENNReal form. -/
theorem s1902LogVolume_smul_form {S : Set (S1902Carrier T)}
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T ≠ ⊤)
    (hm0 : rootExtensionProductHaar T S ≠ 0)
    (hmT : rootExtensionProductHaar T S ≠ ⊤) :
    s1902LogVolume T S =
      ENNReal.ofReal (Real.log (s1902HaarScale T).toReal +
        Real.log (rootExtensionProductHaar T S).toReal) := by
  have hmul : s1902NormalizedHaar T S =
      s1902HaarScale T * rootExtensionProductHaar T S := s1902NormalizedHaar_apply T S
  have hfin : s1902NormalizedHaar T S < ⊤ := by
    rw [hmul]
    exact ENNReal.mul_lt_top hcT.lt_top hmT.lt_top
  have hcne : (s1902HaarScale T).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hc0, hcT⟩
  have hmne : (rootExtensionProductHaar T S).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hm0, hmT⟩
  unfold s1902LogVolume
  rw [haarLogVolume_of_lt_top hfin, hmul, ENNReal.toReal_mul]
  congr 1
  exact Real.log_mul hcne hmne

/-- B2 status rows. -/
def b2Rows : List (String × String) :=
  [ ("measure split", "s1902NormalizedHaar_apply: s1902HaarScale * productHaar")
  , ("log split", "s1902LogVolume_smul_form: ofReal (log scale + log product-Haar) — exact ENNReal form")
  , ("remaining B1", "product-Haar singleton nullity (hull lane; stage4 B1 abstract reduction)")
  , ("remaining B3", "log arithmetic for the local factors (stage4 B3: PROVED)")
  ]

/-- The B2 record has four rows. -/
theorem b2Rows_length : b2Rows.length = 4 := rfl

#check s1902NormalizedHaar_apply
#check s1902LogVolume_smul_form
#check b2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4CorrectedRegionB2SupportActual
end
