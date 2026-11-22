import tmp.sheaf.xif.paper.S355OrbifoldRootStackCandidateActual
import Mathlib.CategoryTheory.Groupoid

-- S356: non-degenerate action groupoid: objects = algebraic-closure roots,
-- morphisms = mu_{2l}; no quotient, root data preserved.  The monoid/section
-- carrier required by S346 remains an exact missing object.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S356RootStackActionGroupoidActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S330QVFamilyRootCardActual
open LeanFormal.IUT.XiFPaper.S355OrbifoldRootStackCandidateActual
open CategoryTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev RootObj : Type := CandidateRoots T b

instance rootStackCategory : Category (RootObj T b) where
  Hom r s := {ζ : rootsOfUnity (n (l := l)) (AC T b) // ζ • r = s}
  id r := ⟨1, one_smul _ _⟩
  comp f g := ⟨g.1 * f.1, by
    simpa [mul_smul, f.2, g.2]⟩
  id_comp f := Subtype.ext (by simp)
  comp_id f := Subtype.ext (by simp)
  assoc f g h := Subtype.ext (by simp [mul_assoc])

instance rootStackGroupoid : Groupoid (RootObj T b) where
  inv f := ⟨f.1⁻¹, by
    simpa [← mul_smul, inv_mul_cancel] using congrArg (fun z => f.1⁻¹ • z) f.2.symm⟩
  inv_comp f := Subtype.ext (by
    show f.1 * f.1⁻¹ = (1 : rootsOfUnity (n (l := l)) (AC T b))
    rw [mul_inv_cancel])
  comp_inv f := Subtype.ext (by
    show f.1⁻¹ * f.1 = (1 : rootsOfUnity (n (l := l)) (AC T b))
    rw [inv_mul_cancel])

noncomputable def rootObj : RootObj T b := candidateRootSubtype T b

-- Actual action-groupoid data: root objects and mu morphisms, no quotient.
structure RootStackActionGroupoidData (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) where
  obj : Type
  [category : Category obj]
  [groupoid : Groupoid obj]
  rootObject : obj

noncomputable def rootStackActionGroupoidData : RootStackActionGroupoidData T b where
  obj := RootObj T b
  category := rootStackCategory T b
  groupoid := rootStackGroupoid T b
  rootObject := rootObj T b

-- Exact missing non-degenerate S346 monoid/section carrier: objects must inject,
-- root/q sections must satisfy the paper power relation.
structure RootStackMonoidSectionCarrier where
  carrier : Type u
  [monoid : Monoid carrier]
  objToCarrier : RootObj T b → carrier
  objToCarrier_injective : Function.Injective objToCarrier
  qSection : carrier
  rootSection : carrier
  qSection_toCompletion : carrier → Completion (qVFamilyPlace T b)
  qSection_toCompletion_q : qSection_toCompletion qSection = (qVFamily T b).q
  rootSection_pow : rootSection ^ (2 * l.value) = qSection
  mu2lAction : (rootsOfUnity (n (l := l)) (AC T b)) → carrier → carrier

#check RootObj
#check rootStackGroupoid
#check rootObj
#check rootStackActionGroupoidData
#check RootStackMonoidSectionCarrier

end LeanFormal.IUT.XiFPaper.S356RootStackActionGroupoidActual

end