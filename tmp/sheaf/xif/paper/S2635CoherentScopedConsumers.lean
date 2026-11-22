import tmp.sheaf.xif.paper.S2634CoherentScopedFieldActual
import tmp.sheaf.xif.paper.S2092FiniteEtaleStackMorphismActual
import tmp.sheaf.xif.paper.S2087ToAObstructionActual
import tmp.sheaf.xif.paper.S2086ToAAssemblyActual
import tmp.sheaf.xif.paper.S2058D6FiniteEtaleActual

/-! # S2635: coherent-scoped S2092 / S2087 / S2086 consumers -/

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
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2092FiniteEtaleStackMorphismActual
open LeanFormal.IUT.XiFPaper.S2087ToAObstructionActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2634CoherentScopedFieldActual

namespace LeanFormal.IUT.XiFPaper.S2635CoherentScopedConsumers

universe u

/-- Coherent-scoped S2092: only `y` is the structure map of a coherent cover. -/
def S2092CoherentScoped : Type 1 :=
  ∀ (C : CoherentCover) {X : EtaleStackOverField S1726K}
    (m : X.Hom C.cover.source) (x : X.Hom S1726Orbicurve.stack),
    Iso (Pseudofunctor.StrongTrans.vcomp m C.cover.map) x →
    EtaleStackFiniteEtaleMorphism x →
    EtaleStackFiniteEtaleMorphism m

noncomputable def morphismOfFiniteEtaleStacksOnCoherent
    (F : CoherentScopedField) : S2092CoherentScoped := by
  intro C X m x e hx
  let hx' : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.vcomp m C.cover.map) :=
    S2058IsoInvarianceFiniteEtale e.symm hx
  refine { baseChange := ?_, hasProperty := ?_ }
  · intro T ptY
    exact (presentationOfCoherentScoped F C m T ptY
      (C.cover.finiteEtale.baseChange T
        (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map))
      (hx'.baseChange T
        (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map))
      (C.cover.finiteEtale.hasProperty T
        (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map)).1
      (C.cover.finiteEtale.hasProperty T
        (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map)).2
      (hx'.hasProperty T
        (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map)).1
      (hx'.hasProperty T
        (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map)).2).1
  · intro T ptY
    exact (presentationOfCoherentScoped F C m T ptY
      (C.cover.finiteEtale.baseChange T
        (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map))
      (hx'.baseChange T
        (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map))
      (C.cover.finiteEtale.hasProperty T
        (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map)).1
      (C.cover.finiteEtale.hasProperty T
        (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map)).2
      (hx'.hasProperty T
        (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map)).1
      (hx'.hasProperty T
        (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map)).2).2

/-- Coherent-scoped S2087 field: only coherent covers are quantified. -/
def S2087GMapFiniteEtaleOnCoherent : Type 1 :=
  ∀ (A B C : CoherentCover) (g : S1728CoverMap B.cover C.cover),
    EtaleStackFiniteEtaleMorphism g.map

noncomputable def gMapFiniteEtaleOnCoherent
    (h : S2092CoherentScoped) : S2087GMapFiniteEtaleOnCoherent :=
  fun A B C g => h C g.map B.cover.map g.commutes B.cover.finiteEtale

/-- Coherent-scoped S2086 cospan field. -/
def S2086CospanGMapFiniteEtaleOnCoherent : Type 1 :=
  ∀ (A B C : CoherentCover)
    (f : S1728CoverMap A.cover C.cover)
    (g : S1728CoverMap B.cover C.cover),
    EtaleStackFiniteEtaleMorphism g.map

noncomputable def cospanGMapFiniteEtaleOnCoherent
    (h : S2092CoherentScoped) :
    S2086CospanGMapFiniteEtaleOnCoherent :=
  fun A B C f g => gMapFiniteEtaleOnCoherent h A B C g

#check S2092CoherentScoped
#check morphismOfFiniteEtaleStacksOnCoherent
#check S2086CospanGMapFiniteEtaleOnCoherent
#check cospanGMapFiniteEtaleOnCoherent
#print axioms morphismOfFiniteEtaleStacksOnCoherent
#print axioms cospanGMapFiniteEtaleOnCoherent

end LeanFormal.IUT.XiFPaper.S2635CoherentScopedConsumers
end
