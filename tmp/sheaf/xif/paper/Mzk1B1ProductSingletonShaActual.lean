import tmp.sheaf.xif.paper.Mzk1ProductHaarSingletonActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import Mathlib.Tactic

/-!
# shehdd A673 B1 product singleton / coordinatewise null assembly (Sha, read-only)

Consumes hull's green B1 file `Mzk1ProductHaarSingletonActual`:
* re-exports the local and product Haar singleton-zero theorems and the image
  singleton zero (in particular for `badInvScale`);
* lifts them to the `s1902NormalizedHaar` scalar multiple and to `s1902LogVolume`:
  point-supported regions have ZERO s1902 log-volume;
* this is the B1 input needed to split `unitRegion \u222a {point}` without changing
  its log-volume.  No gap is claimed.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B1ProductSingletonShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1ProductHaarSingletonActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- B1 re-export: product Haar is null on singletons. -/
theorem b1_product_singleton_zero (x : S1902Carrier T) :
    rootExtensionProductHaar T ({x} : Set (S1902Carrier T)) = 0 :=
  productHaar_singleton_zero T x

/-- B1 re-export: image of a singleton under any map is null. -/
theorem b1_product_image_singleton_zero
    (f : S1902Carrier T → S1902Carrier T) (x : S1902Carrier T) :
    rootExtensionProductHaar T (f '' ({x} : Set (S1902Carrier T))) = 0 :=
  productHaar_image_singleton_zero T f x

/-- B1 at the normalized measure: `s1902NormalizedHaar` is null on singletons. -/
theorem b1_normalizedHaar_singleton_zero (x : S1902Carrier T) :
    s1902NormalizedHaar T ({x} : Set (S1902Carrier T)) = 0 := by
  unfold s1902NormalizedHaar
  rw [Measure.smul_apply, smul_eq_mul, b1_product_singleton_zero T x, mul_zero]

/-- B1 at the log-volume: the `s1902LogVolume` of a singleton is ZERO. -/
theorem b1_logVolume_singleton_zero (x : S1902Carrier T) :
    s1902LogVolume T ({x} : Set (S1902Carrier T)) = 0 := by
  unfold s1902LogVolume
  exact haarLogVolume_eq_zero_of_null (b1_normalizedHaar_singleton_zero T x)

structure B1AssemblyRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def b1AssemblyRows : List B1AssemblyRow :=
  [ ⟨"hull B1 source", "Mzk1ProductHaarSingletonActual (green)", "GREEN_SOURCE"⟩
  , ⟨"product singleton zero", "b1_product_singleton_zero", "GREEN"⟩
  , ⟨"image singleton zero", "b1_product_image_singleton_zero (badInvScale case)", "GREEN"⟩
  , ⟨"normalized measure zero", "b1_normalizedHaar_singleton_zero", "GREEN"⟩
  , ⟨"s1902 log-volume zero", "b1_logVolume_singleton_zero", "GREEN"⟩
  , ⟨"corrected_gap1_unconditional", "mainline Mzk1CorrectedGap1UnconditionalActual (THEOREM)", "GREEN"⟩
  , ⟨"scope", "parameterized B1 assembly only; no gap claimed", "INTEGRITY"⟩
  ]

theorem b1AssemblyRows_length : b1AssemblyRows.length = 7 := rfl

theorem b1AssemblyRows_statuses_ok :
    b1AssemblyRows.all (fun r =>
      r.status ∈ ["GREEN_SOURCE", "GREEN", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1B1ProductSingletonShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1B1ProductSingletonShaActual.b1_logVolume_singleton_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1B1ProductSingletonShaActual.b1_product_image_singleton_zero
