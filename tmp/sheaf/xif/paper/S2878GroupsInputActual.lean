import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2878GroupsInputActual

universe u

/-- Explicit input package for `SourceOrbicurveGroupData.ofFundamentalGroup`.
Nothing is constructed from arithmetic data; all four source inputs are fields. -/
structure GroupsInput
    {F : Type u} [Field F]
    (X : Iut.HyperbolicOrbicurve F)
    (G : ProfiniteGrp.{u}) where
  arithmeticGroup : ProfiniteGrp.{u}
  arithmetic : Iut.OrbicurveEtaleFundamentalGroup X arithmeticGroup
  projection : arithmeticGroup ⟶ G
  projection_surjective : Function.Surjective projection
  geometric : Iut.OrbicurveEtaleFundamentalGroup X
    (Iut.closedSubgroupProfiniteGrp
      (Iut.profiniteKernelClosedSubgroup projection))

noncomputable def GroupsInput.toSourceOrbicurveGroupData
    {F : Type u} [Field F]
    {X : Iut.HyperbolicOrbicurve F} {G : ProfiniteGrp.{u}}
    (D : GroupsInput X G) :
    InitialThetaSource.SourceOrbicurveGroupData X G :=
  InitialThetaSource.SourceOrbicurveGroupData.ofFundamentalGroup
    D.arithmeticGroup D.arithmetic D.projection
    D.projection_surjective D.geometric

@[simp] theorem GroupsInput.toSourceOrbicurveGroupData_groups
    {F : Type u} [Field F]
    {X : Iut.HyperbolicOrbicurve F} {G : ProfiniteGrp.{u}}
    (D : GroupsInput X G) :
    (D.toSourceOrbicurveGroupData).groups =
      { arithmeticGroup := D.arithmeticGroup
        arithmetic := D.arithmetic
        projection := D.projection
        projection_surjective := D.projection_surjective
        geometric := D.geometric } :=
  rfl

#check GroupsInput
#check GroupsInput.toSourceOrbicurveGroupData
#print axioms GroupsInput.toSourceOrbicurveGroupData
#print axioms GroupsInput.toSourceOrbicurveGroupData_groups

end LeanFormal.IUT.XiFPaper.S2878GroupsInputActual
end
