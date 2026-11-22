import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S2558ConcreteWitnessPlanActual
import tmp.sheaf.xif.paper.S2559ConcreteWitnessRefinementPlanActual
import tmp.sheaf.xif.paper.S2561S2512LiftUniqueActual
import tmp.sheaf.xif.paper.S2517InvObjActual
import tmp.sheaf.xif.paper.S2480QiActual

/-! # S2628: lift uniqueness -> cone essential surjectivity; S2517 strong cover -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2558ConcreteWitnessPlanActual
open LeanFormal.IUT.XiFPaper.S2559ConcreteWitnessRefinementPlanActual
open LeanFormal.IUT.XiFPaper.S2561S2512LiftUniqueActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace LeanFormal.IUT.XiFPaper.S2628CoherentConstructionActual

universe u

variable {F : Type u} [Field F]

theorem coneEssSurj_of_liftUnique
    {source target : EtaleStackOverField F}
    {map : source.Hom target}
    {T : SchemeOverField F}
    {pt : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F T) target.fiber}
    (P : EtaleStackBaseChangePresentation map T pt)
    (h : S2558LiftUnique (S1852WeakSquare P) P.isPullback) :
    S1852ConeEssSurj P := by
  intro W c f hX hY
  obtain ⟨eX⟩ := hX
  obtain ⟨eY⟩ := hY
  exact h W c f (P.isPullback.lift W c)
    ⟨eX, eY⟩
    ⟨P.isPullback.liftToX W c, P.isPullback.liftToY W c⟩

section Qi

variable (C : FiniteEtaleCover S2482AffineScheme)
variable (T : SchemeOverField S2480QiActual.F)
variable (q : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S2480QiActual.F T)
  S2482Orbicurve.stack.fiber)

noncomputable def s2517StrongBc :
    StrongEtaleStackBaseChangePresentation
      (S2517InvObj C).map T q where
  toWeak := (S2517InvObj C).finiteEtale.baseChange T q
  coneEssSurj := by
    apply coneEssSurj_of_liftUnique
    simpa only [S2559HasLiftUnique, S1852WeakSquare] using
      S2561S2517HasLiftUnique C T q

noncomputable def s2517StrongFiniteEtale :
    StrongEtaleStackFiniteEtaleMorphism (S2517InvObj C).map where
  baseChange T q := s2517StrongBc C T q
  hasProperty T q := (S2517InvObj C).finiteEtale.hasProperty T q

noncomputable def s2517StrongCover :
    StrongCover S2482Orbicurve where
  source := (S2517InvObj C).source
  map := (S2517InvObj C).map
  finiteEtale := s2517StrongFiniteEtale C

end Qi

#check coneEssSurj_of_liftUnique
#check s2517StrongCover
#print axioms coneEssSurj_of_liftUnique
#print axioms s2517StrongCover

end LeanFormal.IUT.XiFPaper.S2628CoherentConstructionActual
end
