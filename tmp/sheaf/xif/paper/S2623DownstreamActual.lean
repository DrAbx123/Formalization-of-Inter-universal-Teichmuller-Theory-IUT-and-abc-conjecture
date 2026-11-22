import tmp.sheaf.xif.paper.S2621FieldWithHypothesesActual
import tmp.sheaf.xif.paper.S2096StackMorphismActual

/-! # S2623: downstream from corrected field with finite hypotheses -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2620M1CoherenceFields
open LeanFormal.IUT.XiFPaper.S2621FieldWithHypothesesActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2087ToAObstructionActual
open LeanFormal.IUT.XiFPaper.S2091SchemeDirectActual
open LeanFormal.IUT.XiFPaper.S2092FiniteEtaleStackMorphismActual
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual

namespace LeanFormal.IUT.XiFPaper.S2623DownstreamActual

universe u

noncomputable def morphismOfFiniteEtaleStacks
    (h : BaseChangePresentationFieldWithHypotheses) :
    S2092MorphismOfFiniteEtaleStacks := by
  intro X Y Z m y x e hx hy
  let hx' : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.vcomp m y) :=
    S2058IsoInvarianceFiniteEtale e.symm hx
  refine { baseChange := ?_, hasProperty := ?_ }
  · intro T ptY
    exact (h m y T ptY
      (hy.baseChange T (Pseudofunctor.StrongTrans.vcomp ptY y))
      (hx'.baseChange T (Pseudofunctor.StrongTrans.vcomp ptY y))
      (hy.hasProperty T (Pseudofunctor.StrongTrans.vcomp ptY y)).1
      (hy.hasProperty T (Pseudofunctor.StrongTrans.vcomp ptY y)).2
      (hx'.hasProperty T (Pseudofunctor.StrongTrans.vcomp ptY y)).1
      (hx'.hasProperty T (Pseudofunctor.StrongTrans.vcomp ptY y)).2).1
  · intro T ptY
    exact (h m y T ptY
      (hy.baseChange T (Pseudofunctor.StrongTrans.vcomp ptY y))
      (hx'.baseChange T (Pseudofunctor.StrongTrans.vcomp ptY y))
      (hy.hasProperty T (Pseudofunctor.StrongTrans.vcomp ptY y)).1
      (hy.hasProperty T (Pseudofunctor.StrongTrans.vcomp ptY y)).2
      (hx'.hasProperty T (Pseudofunctor.StrongTrans.vcomp ptY y)).1
      (hx'.hasProperty T (Pseudofunctor.StrongTrans.vcomp ptY y)).2).2

noncomputable def gMapFiniteEtaleField
    (h : BaseChangePresentationFieldWithHypotheses) :
    S2087GMapFiniteEtaleField :=
  S2092GMapFiniteEtaleOfMorphismOfFiniteEtaleStacks
    (morphismOfFiniteEtaleStacks h)

noncomputable def cospanGMapFiniteEtaleField
    (h : BaseChangePresentationFieldWithHypotheses) :
    S2087CospanGMapFiniteEtaleField := by
  intro A B C f g
  exact gMapFiniteEtaleField h A B C g

noncomputable def s2086CospanGMapFiniteEtale
    (h : BaseChangePresentationFieldWithHypotheses) :
    S2086CospanGMapFiniteEtale := by
  intro A B C f g
  exact gMapFiniteEtaleField h A B C g

noncomputable def d6FiniteEtale
    (h : BaseChangePresentationFieldWithHypotheses)
    (hpb : S2086BaseChangePullback (s2086CospanGMapFiniteEtale h))
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) :=
  S2086D6FiniteEtaleOfInputs (s2086CospanGMapFiniteEtale h) hpb f g

#check morphismOfFiniteEtaleStacks
#check d6FiniteEtale
#print axioms morphismOfFiniteEtaleStacks
#print axioms d6FiniteEtale

end LeanFormal.IUT.XiFPaper.S2623DownstreamActual
end
