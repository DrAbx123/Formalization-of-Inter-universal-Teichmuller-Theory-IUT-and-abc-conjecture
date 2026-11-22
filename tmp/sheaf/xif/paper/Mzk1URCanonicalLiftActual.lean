/- Canonical bad-place lift (kurt, R1): make the F-side lift DEFINED by contraction of the actual
K-section place, so that the place identification with the qVFam-side place is rfl and the
alignment hypothesis `NativeBadLiftAlignment` disappears (assessment only: the original
`nativeBadLift` is Classical.choose-based and is NOT changed here).
-/
import tmp.sheaf.xif.paper.Mzk1BaseChangeQCorrespondenceActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URCanonicalLiftActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1BaseChangeQCorrespondenceActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- The canonical F-side bad-place lift: contraction of the actual K-section place. -/
noncomputable def nativeBadLiftCanonical (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.F :=
  nativeBaseContractionFPlace T b

/-- Its defining property: it is the contraction of the K-section place (rfl). -/
theorem nativeBadLiftCanonical_comap (b : Bad (nativePlaceSelection T)) :
    NumberFieldFinitePlace.comap (k := T.arithmetic.F) (nativeBaseSectionPlace T b) =
      nativeBadLiftCanonical (T := T) b := rfl

/-- The canonical lift lies over the bad moduli place. -/
theorem nativeBadLiftCanonical_comap_Fmod (b : Bad (nativePlaceSelection T)) :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (nativeBadLiftCanonical (T := T) b) =
      b.1 := by
  unfold nativeBadLiftCanonical
  exact nativeBaseContractionFPlace_comap T b

/-- ASSESSMENT: with the canonical lift the alignment `NativeBadLiftAlignment` is rfl. -/
theorem canonicalLift_alignment (b : Bad (nativePlaceSelection T)) :
    nativeBaseContractionFPlace T b = nativeBadLiftCanonical (T := T) b := rfl

/-- qVFam-side place built from the canonical lift. -/
noncomputable def canonicalQFamTensorPlace (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.F :=
  nativeBadLiftCanonical (T := T) b

/-- Identifiability of the qVFam place with the contraction place, by definition. -/
theorem canonicalQFamTensorPlace_eq_contraction (b : Bad (nativePlaceSelection T)) :
    canonicalQFamTensorPlace (T := T) b = nativeBaseContractionFPlace T b := rfl

#print axioms nativeBadLiftCanonical_comap
#print axioms nativeBadLiftCanonical_comap_Fmod
#print axioms canonicalLift_alignment
#print axioms canonicalQFamTensorPlace_eq_contraction

end LeanFormal.IUT.XiFPaper.Mzk1URCanonicalLiftActual
end