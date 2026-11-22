import tmp.sheaf.xif.paper.S2046FiniteEtaleAPIGapActual
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S2046FiniteEtaleAPIGapActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S3129FiniteEtaleCompositionAttempt

/-- The composition-closure target for representably finite-etale stack maps. -/
def S3129CompositionTarget (F : Type) [Field F] : Type 1 :=
  forall {W Y Z : EtaleStackOverField F}
    (f : W.Hom Y) (g : Y.Hom Z),
    EtaleStackFiniteEtaleMorphism f ->
    EtaleStackFiniteEtaleMorphism g ->
    EtaleStackFiniteEtaleMorphism (Pseudofunctor.StrongTrans.vcomp f g)

#check @S2046CompositionStatement
#check @EtaleStackFiniteEtaleMorphism
#check @EtaleStackRepresentableMorphismProperty
#check AlgebraicGeometry.IsFinite.comp
#check AlgebraicGeometry.Etale.comp
#check @S3129CompositionTarget
#check @EtalePseudofunctorSquare.TwoPullbackWitness
#check EtaleStackBaseChangePresentation

example {S T U : AlgebraicGeometry.Scheme} (f : S ⟶ T) (g : T ⟶ U)
    [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsFinite g] :
    AlgebraicGeometry.IsFinite (f ≫ g) := inferInstance

example {S T U : AlgebraicGeometry.Scheme} (f : S ⟶ T) (g : T ⟶ U)
    [AlgebraicGeometry.Etale f] [AlgebraicGeometry.Etale g] :
    AlgebraicGeometry.Etale (f ≫ g) := inferInstance

end LeanFormal.IUT.XiFPaper.S3129FiniteEtaleCompositionAttempt
end