/- R1 probe (kurt): does the tree have the IsFractionRing instance needed for the DVR
unit-times-zpow decomposition of nonzero elements of the root extension L?

Mathlib: IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
  {K} [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} (hirr) {x : K} (hx) :
    ∃ (n : ℤ) (u : Rˣ), x = u • algebraMap R K ϖ ^ n
with R := Integers (rootNormedExtension T b), K := rootNormedExtension T b.
If this probe compiles, R1's value-group decomposition needs NO new obligation; only the
general Haar-scaling lemma remains.
-/
import tmp.sheaf.xif.paper.PaperRootExtensionDiscreteValuationActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1URRootValueGroupProbeActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootExtensionDiscreteValuationActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Value-group decomposition of a nonzero element of the actual root extension. -/
theorem urRoot_valueGroup_decomp (x : rootNormedExtension T b) (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : (Integers (rootNormedExtension T b))ˣ),
      x = u • algebraMap (Integers (rootNormedExtension T b)) (rootNormedExtension T b)
        (rootUniformizer T b) ^ n :=
  IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (rootUniformizer_irreducible (T := T) (b := b)) hx

#print axioms urRoot_valueGroup_decomp

end LeanFormal.IUT.XiFPaper.Mzk1URRootValueGroupProbeActual
end