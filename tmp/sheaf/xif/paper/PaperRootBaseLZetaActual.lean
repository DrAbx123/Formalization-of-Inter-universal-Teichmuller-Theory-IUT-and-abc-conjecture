import tmp.sheaf.xif.paper.PaperRootLValuedTensorCarrierActual
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

-- S231: finite complete LZeta built over the complete rootBase, containing
-- both the 2l-th root of q and zeta_{2l}; avoids the missing RootL-algebra
-- instance by adjoining both generators over rootBase.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperRootBaseLZetaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def rootBaseZeta : rootNormedAmbient T b :=
  Classical.choose (HasEnoughRootsOfUnity.exists_primitiveRoot
    (rootNormedAmbient T b) (2 * l.value))

theorem rootBaseZeta_pow : rootBaseZeta T b ^ (2 * l.value) = 1 :=
  (Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot
    (rootNormedAmbient T b) (2 * l.value))).pow_eq_one

theorem rootBaseZeta_isIntegral :
    IsIntegral (rootBase T b) (rootBaseZeta T b) := by
  have hpow : IsIntegral (rootBase T b) ((rootBaseZeta T b) ^ (2 * l.value)) := by
    rw [rootBaseZeta_pow]
    exact isIntegral_algebraMap
  exact IsIntegral.of_pow (by exact Nat.mul_pos (by norm_num) l.prime.pos) hpow

noncomputable def rootBaseZetaGenerators : Set (rootNormedAmbient T b) :=
  {rootNormedElement T b, rootBaseZeta T b}

theorem rootBaseZetaGenerators_isIntegral :
    ∀ x ∈ rootBaseZetaGenerators (T := T) (b := b),
      IsIntegral (rootBase T b) x := by
  intro x hx
  simp only [rootBaseZetaGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact rootNormedElement_isIntegral (T := T) (b := b)
  · exact rootBaseZeta_isIntegral (T := T) (b := b)

abbrev RootBaseLZetaField : IntermediateField (rootBase T b) (rootNormedAmbient T b) :=
  IntermediateField.adjoin (rootBase T b) (rootBaseZetaGenerators (T := T) (b := b))

abbrev RootBaseLZeta : Type := RootBaseLZetaField T b

instance rootBaseLZetaField : Field (RootBaseLZeta T b) := inferInstance

noncomputable instance rootBaseLZetaNormedField : NormedField (RootBaseLZeta T b) := inferInstance

noncomputable instance rootBaseLZetaFiniteDimensional :
    FiniteDimensional (rootBase T b) (RootBaseLZeta T b) := by
  have hfin : (rootBaseZetaGenerators (T := T) (b := b)).Finite := by
    rw [rootBaseZetaGenerators]
    exact Set.Finite.insert _ (Set.finite_singleton _)
  haveI : Fintype (rootBaseZetaGenerators (T := T) (b := b)) := hfin.fintype
  exact IntermediateField.finiteDimensional_adjoin
    (K := rootBase T b) (S := rootBaseZetaGenerators (T := T) (b := b))
    (rootBaseZetaGenerators_isIntegral (T := T) (b := b))

noncomputable instance rootBaseLZetaCompleteSpace : CompleteSpace (RootBaseLZeta T b) := by
  haveI : FiniteDimensional (rootBase T b) (RootBaseLZeta T b) :=
    rootBaseLZetaFiniteDimensional T b
  exact FiniteDimensional.complete (rootBase T b) (RootBaseLZeta T b)

noncomputable instance rootBaseLZetaProperSpace : ProperSpace (RootBaseLZeta T b) := by
  exact @FiniteDimensional.proper (rootBase T b) inferInstance (RootBaseLZeta T b)
    inferInstance inferInstance inferInstance (rootBaseLZetaFiniteDimensional T b)

noncomputable instance rootBaseLZetaMeasurableSpace : MeasurableSpace (RootBaseLZeta T b) :=
  borel _

#check RootBaseLZeta
#check rootBaseLZetaFiniteDimensional
#check rootBaseLZetaCompleteSpace
#check rootBaseLZetaProperSpace

end LeanFormal.IUT.XiFPaper.PaperRootBaseLZetaActual

end