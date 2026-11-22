import tmp.sheaf.xif.paper.S1843SourceAllPointsActual

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Probe

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1843SourceAllPointsActual

example (Q : SchemeOverField S1726K) (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (S1743Y Q).obj U = Cat.of (Discrete (Opposite.unop U.as ⟶ Q)) := rfl

#check @Pseudofunctor.StrongTrans.isoMk
#check @CategoryTheory.Cat.Hom.isoMk
#check @RingHom.fst
#check @RingHom.snd
#check @RingHom.prod
#check @RingEquiv.prodComm
#check @Over.homMk
#check @Over.OverMorphism.ext
#check @Spec.map_comp
#check @AlgebraicGeometry.Spec.map_injective
#check @Over.w
#check @Over.comp_left
#check @Over.mk
#check @S1726AffineScheme
#check @S1726AffineOver
#check @S1726CoordinateRing

end Probe
