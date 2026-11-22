import tmp.sheaf.xif.paper.S1892PullbackFiniteEtaleActual

noncomputable section
open CategoryTheory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1892PullbackFiniteEtaleActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2542TransportE1E4Actual

universe u
variable {F : Type u} [Field F]
variable {W Z : Iut.EtaleStackOverField F}
variable {f g : W.Hom Z} (e : Iso f g)
variable {T : Iut.SchemeOverField F}
variable {q : Pseudofunctor.StrongTrans
  (Iut.schemeRepresentableEtalePseudofunctor F T) Z.fiber}
variable (P : Iut.EtaleStackBaseChangePresentation f T q)

/-- E1: the new commutativity 2-iso for the transported map `g`. -/
noncomputable def S2542NewCommutes :
    Iso (Pseudofunctor.StrongTrans.vcomp P.toSource g)
      (Pseudofunctor.StrongTrans.vcomp P.projectionMap.transformation q) := by
  let Bicat := Iut.EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  exact (@Bicategory.whiskerLeftIso Bicat _
    (Iut.schemeRepresentableEtalePseudofunctor F P.pullbackScheme)
    W.fiber Z.fiber P.toSource f g e).symm.trans P.commutes

/-- E4: the projection is unchanged, so its finite-etale property is reused. -/
theorem S2542HasProperty
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T) Z.fiber)
    (hf : Iut.EtaleStackFiniteEtaleMorphism f) :
    IsFinite (hf.baseChange T q).projection.left ∧
      Etale (hf.baseChange T q).projection.left :=
  hf.hasProperty T q

#check S2542NewCommutes
#check S2542HasProperty
#print axioms S2542NewCommutes
#print axioms S2542HasProperty
end LeanFormal.IUT.XiFPaper.S2542TransportE1E4Actual
end