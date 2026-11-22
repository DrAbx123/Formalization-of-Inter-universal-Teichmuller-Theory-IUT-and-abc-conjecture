import tmp.sheaf.xif.paper.S2635CoherentScopedConsumers
import tmp.sheaf.xif.paper.S2069D6CompositionClosureActual
import tmp.sheaf.xif.paper.S2048FiniteEtaleCompSchemeActual
import tmp.sheaf.xif.paper.S1955AssembleCDActual
import tmp.sheaf.xif.paper.S1985SiteLiftNaturalityActual
import tmp.sheaf.xif.paper.S2042D6GeometricHalfActual
import tmp.sheaf.xif.paper.S2043D6StructureMapEqActual

/-! # S2636: coherent-scoped S2086 base-change pullback and D6(c) -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual
open LeanFormal.IUT.XiFPaper.S2048FiniteEtaleCompSchemeActual
open LeanFormal.IUT.XiFPaper.S2069D6CompositionClosureActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S1985SiteLiftNaturalityActual
open LeanFormal.IUT.XiFPaper.S2042D6GeometricHalfActual
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2635CoherentScopedConsumers

namespace LeanFormal.IUT.XiFPaper.S2636CoherentScopedD6Actual

universe u

def S2086BaseChangePullbackOnCoherent
    (hg : S2086CospanGMapFiniteEtaleOnCoherent) : Type 1 :=
  ∀ (A B C : CoherentCover)
    (f : S1728CoverMap A.cover C.cover)
    (g : S1728CoverMap B.cover C.cover)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T)
      A.cover.source.fiber),
    (S2086ToASquare f g T ptA
      ((hg A B C f g).baseChange T (S2086PointC f ptA))).TwoPullbackWitness

def S2044ToAFiniteEtaleFieldOnCoherent : Type 1 :=
  ∀ (A B C : CoherentCover)
    (f : S1728CoverMap A.cover C.cover)
    (g : S1728CoverMap B.cover C.cover),
    EtaleStackFiniteEtaleMorphism
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := A.cover.source) (toA f g)

noncomputable def toAOnCoherentOfInputs
    (hg : S2086CospanGMapFiniteEtaleOnCoherent)
    (h : S2086BaseChangePullbackOnCoherent hg) :
    S2044ToAFiniteEtaleFieldOnCoherent := by
  intro A B C f g
  refine { baseChange := ?_, hasProperty := ?_ }
  · intro T ptA
    exact S2086ToAPresentation f g T ptA
      ((hg A B C f g).baseChange T (S2086PointC f ptA))
      (h A B C f g T ptA)
  · intro T ptA
    exact (hg A B C f g).hasProperty T (S2086PointC f ptA)

noncomputable def D6FiniteEtaleOnCoherent
    (hg : S2086CospanGMapFiniteEtaleOnCoherent)
    (h : S2086BaseChangePullbackOnCoherent hg)
    (A B C : CoherentCover)
    (f : S1728CoverMap A.cover C.cover)
    (g : S1728CoverMap B.cover C.cover) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) := by
  have hto : EtaleStackFiniteEtaleMorphism
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := A.cover.source) (toA f g) :=
    toAOnCoherentOfInputs hg h A B C f g
  have hto : EtaleStackFiniteEtaleMorphism
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := A.cover.source) (toA f g) :=
    toAOnCoherentOfInputs hg h A B C f g
  have hA : EtaleStackFiniteEtaleMorphism A.map :=
    A.cover.finiteEtale
  change EtaleStackFiniteEtaleMorphism
    (source := S2042IsoCommaStackObj (f := f) (g := g))
    (target := S1726Orbicurve.stack) (structureMap f g)
  refine { baseChange := ?_, hasProperty := ?_ }
  · intro T ptA
    exact EtaleStackBaseChangePresentation.comp
      (Pg := hA.baseChange T ptA)
      (Pf := hto.baseChange (hA.baseChange T ptA).pullbackScheme
        (hA.baseChange T ptA).toSource)
  · intro T ptA
    let Pg := hA.baseChange T ptA
    let Pf := hto.baseChange Pg.pullbackScheme Pg.toSource
    have hf' : AlgebraicGeometry.IsFinite Pf.projection.left ∧
        AlgebraicGeometry.Etale Pf.projection.left :=
      hto.hasProperty Pg.pullbackScheme Pg.toSource
    have hg' : AlgebraicGeometry.IsFinite Pg.projection.left ∧
        AlgebraicGeometry.Etale Pg.projection.left :=
      hA.hasProperty T ptA
    haveI := hf'.1
    haveI := hf'.2
    haveI := hg'.1
    haveI := hg'.2
    exact S2048_isFinite_and_etale_comp
      (f := Pf.projection.left) (g := Pg.projection.left)

#check S2086BaseChangePullbackOnCoherent
#check toAOnCoherentOfInputs
#check D6FiniteEtaleOnCoherent
#print axioms D6FiniteEtaleOnCoherent

end LeanFormal.IUT.XiFPaper.S2636CoherentScopedD6Actual
end
