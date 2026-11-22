import tmp.sheaf.xif.paper.S2632S1726SplitCoverStrongActual
import tmp.sheaf.xif.paper.S2559ConcreteWitnessRefinementPlanActual

/-! # S2633: S1726 split cover consumers (coneEssSurj, lift uniqueness) -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2558ConcreteWitnessPlanActual
open LeanFormal.IUT.XiFPaper.S2559ConcreteWitnessRefinementPlanActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1866ApexCoherenceActual
open LeanFormal.IUT.XiFPaper.S2632S1726SplitCoverStrongActual

namespace LeanFormal.IUT.XiFPaper.S2633S1726SplitConsumers

theorem S1726SplitConeEssSurj
    (T : Iut.SchemeOverField S1726K)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor S1726K T)
      S1726Orbicurve.stack.fiber) :
    S1852ConeEssSurj (S1726SplitPresentation T q) := by
  have h := (S1866StrongCoverOf_iff_baseChange S1726SplitCover).mp
    S1726SplitStrongCoverOf T q
  simpa [S1726SplitCover, S1726SplitStrongFiniteEtale,
    S1726SplitStrongBc, S1726SplitPresentation] using h

theorem liftUnique_of_coneEssSurj
    {F : Type} [Field F]
    {source target : EtaleStackOverField F}
    {map : source.Hom target}
    {T : SchemeOverField F}
    {pt : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F T) target.fiber}
    (P : EtaleStackBaseChangePresentation map T pt)
    (h : S1852ConeEssSurj P) :
    S2558LiftUnique (S1852WeakSquare P) P.isPullback := by
  intro W c L1 L2 h1 h2
  obtain ⟨e1⟩ := h W c L1 (Nonempty.intro h1.toX) (Nonempty.intro h1.toY)
  obtain ⟨e2⟩ := h W c L2 (Nonempty.intro h2.toX) (Nonempty.intro h2.toY)
  exact ⟨e1.trans e2.symm⟩

theorem S1726SplitHasLiftUnique :
    S2559HasLiftUnique S1726SplitCover.finiteEtale := by
  intro T q
  exact liftUnique_of_coneEssSurj (S1726SplitPresentation T q)
    (S1726SplitConeEssSurj T q)

#check S1726SplitConeEssSurj
#check S1726SplitHasLiftUnique
#print axioms S1726SplitHasLiftUnique

end LeanFormal.IUT.XiFPaper.S2633S1726SplitConsumers
end
