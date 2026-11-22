import tmp.sheaf.xif.paper.S1854CoherentCategoryActual
import tmp.sheaf.xif.paper.S1816OrbicurveCoversToAffineActual
import tmp.sheaf.xif.paper.S1814OrbicurveCoversAffineActual
import tmp.sheaf.xif.paper.S1855RPrimeFiberIntegrationActual
import tmp.sheaf.xif.paper.S1753OrbicurveEtalePiAssemblyActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace ProbeS1868

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual
open LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1855RPrimeFiberIntegrationActual
open LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual

attribute [local instance] S1854CoherentCategory11

noncomputable def G : CoherentCover ⥤ S1779AlgR where
  obj A := S1814AlgEquiv.inverse.obj (S1816Obj A.cover)
  map {A B} f := S1814AlgEquiv.inverse.map
    (S1816Map A.cover B.cover (S1854QuotEquiv A B f))
  map_id A := by
    have hq : S1854QuotEquiv A A (𝟙 A) = 𝟙 A.cover := S1854Forget11.map_id A
    have h16 : S1816Map A.cover A.cover (𝟙 A.cover) = 𝟙 (S1816Obj A.cover) :=
      (S1816Map_id_iff A.cover).mpr (S1852FirstMissingOnCoherent A)
    rw [show S1854QuotEquiv A A (𝟙 A) = 𝟙 A.cover from hq]
    rw [h16]
    exact S1814AlgEquiv.inverse.map_id (S1816Obj A.cover)
  map_comp {A B C} f g := by
    have hq : S1854QuotEquiv A C (f ≫ g) =
        S1854QuotEquiv A B f ≫ S1854QuotEquiv B C g := S1854Forget11.map_comp f g
    rw [hq, S1816Map_comp, S1814AlgEquiv.inverse.map_comp]

#check G
#check G.obj
#check G.map
example (A : CoherentCover) : G.obj A = S1814AlgEquiv.inverse.obj (S1816Obj A.cover) := rfl
example {A B : CoherentCover} (f : A ⟶ B) :
    G.map f = S1814AlgEquiv.inverse.map (S1816Map A.cover B.cover (S1854QuotEquiv A B f)) := rfl

-- faithful
instance : G.Faithful where
  map_injective {A B} f g h := by
    apply (S1854QuotEquiv A B).injective
    apply S1816Map_injective
    exact S1814AlgEquiv.inverse.map_injective h

#check G.Faithful
#check Functor.IsEquivalence

end ProbeS1868
