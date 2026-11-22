import tmp.sheaf.xif.paper.S2134D9DescentActual
import Mathlib.CategoryTheory.Sites.Descent.Precoverage

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2431Probe

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S2103D9PrestackActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual

universe v u v' u'

#check @Pseudofunctor.isStackFor_iff
#check @Pseudofunctor.isStackFor_ofArrows_iff
#check @Pseudofunctor.IsStackFor
#check @Pseudofunctor.IsPrestackFor
#check @Pseudofunctor.IsPrestackFor.fullyFaithful
#check @Pseudofunctor.IsPrestackFor_generate_iff
#check @Pseudofunctor.isPrestackFor_iff_of_sieve_eq
#check @Pseudofunctor.IsStackFor.of_le
#check @Pseudofunctor.IsStackFor.of_le'
#check @Pseudofunctor.isPrestackFor
#check @Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
#check @Precoverage.generate_mem_toGrothendieck
#check @Functor.FullyFaithful.preimageIso
#check @Functor.FullyFaithful.map_injective
#check @Functor.IsEquivalence
#check @Functor.EssSurj
#check @Presieve.isSheafFor_top
#check @Sieve.overEquiv

/-- probe: IsPrestackFor top -/
theorem probe_isPrestackFor_top {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) {S : C} :
    F.IsPrestackFor (⊤ : Presieve S) := by
  have h : (⊤ : Presieve S) = (⊤ : Sieve S).arrows := by simp
  rw [h]
  rw [Pseudofunctor.isPrestackFor_iff_isSheafFor]
  intro M N
  have htop := Presieve.isSheafFor_top (F.presheafHom M N) (X := (Over.mk (𝟙 S)))
  simpa using htop

end LeanFormal.IUT.XiFPaper.S2431Probe
