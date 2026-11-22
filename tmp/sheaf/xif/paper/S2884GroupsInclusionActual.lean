import tmp.sheaf.xif.paper.S2878GroupsInputActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2878GroupsInputActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2884GroupsInclusionActual

universe u

/-- Explicit open-embedding data between the two exact sequences. -/
structure GroupsInclusion
    {F : Type u} [Field F]
    {xF cF : Iut.HyperbolicOrbicurve F}
    {G : ProfiniteGrp.{u}}
    (xFInput : GroupsInput xF G)
    (cFInput : GroupsInput cF G) where
  geometric : Iut.ProfiniteOpenEmbedding
    (xFInput.toSourceOrbicurveGroupData).sequence.geometric
    (cFInput.toSourceOrbicurveGroupData).sequence.geometric
  arithmetic : Iut.ProfiniteOpenEmbedding
    (xFInput.toSourceOrbicurveGroupData).sequence.arithmetic
    (cFInput.toSourceOrbicurveGroupData).sequence.arithmetic
  inclusion_square :
    geometric.hom ≫ (cFInput.toSourceOrbicurveGroupData).sequence.inclusion =
      (xFInput.toSourceOrbicurveGroupData).sequence.inclusion ≫
        arithmetic.hom
  projection_compatible :
    arithmetic.hom ≫ (cFInput.toSourceOrbicurveGroupData).sequence.projection =
      (xFInput.toSourceOrbicurveGroupData).sequence.projection

/-- Package the explicit fields as the source `fGroupInclusion`. -/
noncomputable def GroupsInclusion.toProfiniteFundamentalGroupInclusion
    {F : Type u} [Field F]
    {xF cF : Iut.HyperbolicOrbicurve F}
    {G : ProfiniteGrp.{u}}
    {xFInput : GroupsInput xF G} {cFInput : GroupsInput cF G}
    (D : GroupsInclusion xFInput cFInput) :
    Iut.ProfiniteFundamentalGroupInclusion
      (xFInput.toSourceOrbicurveGroupData).sequence.geometric
      (xFInput.toSourceOrbicurveGroupData).sequence.arithmetic
      (cFInput.toSourceOrbicurveGroupData).sequence.geometric
      (cFInput.toSourceOrbicurveGroupData).sequence.arithmetic
      G
      (xFInput.toSourceOrbicurveGroupData).sequence
      (cFInput.toSourceOrbicurveGroupData).sequence where
  geometric := D.geometric
  arithmetic := D.arithmetic
  inclusion_square := D.inclusion_square
  projection_compatible := D.projection_compatible

/-- A source package carrying both group data and their inclusion. -/
structure CoreGroupsInput
    {F : Type u} [Field F]
    (xF cF : Iut.HyperbolicOrbicurve F)
    (G : ProfiniteGrp.{u}) where
  xFInput : GroupsInput xF G
  cFInput : GroupsInput cF G
  inclusion : GroupsInclusion xFInput cFInput

noncomputable def CoreGroupsInput.xFGroups
    {F : Type u} [Field F]
    {xF cF : Iut.HyperbolicOrbicurve F} {G : ProfiniteGrp.{u}}
    (D : CoreGroupsInput xF cF G) :
    SourceOrbicurveGroupData xF G :=
  D.xFInput.toSourceOrbicurveGroupData

noncomputable def CoreGroupsInput.cFGroups
    {F : Type u} [Field F]
    {xF cF : Iut.HyperbolicOrbicurve F} {G : ProfiniteGrp.{u}}
    (D : CoreGroupsInput xF cF G) :
    SourceOrbicurveGroupData cF G :=
  D.cFInput.toSourceOrbicurveGroupData

noncomputable def CoreGroupsInput.fGroupInclusion
    {F : Type u} [Field F]
    {xF cF : Iut.HyperbolicOrbicurve F} {G : ProfiniteGrp.{u}}
    (D : CoreGroupsInput xF cF G) :
    Iut.ProfiniteFundamentalGroupInclusion
      D.xFGroups.sequence.geometric D.xFGroups.sequence.arithmetic
      D.cFGroups.sequence.geometric D.cFGroups.sequence.arithmetic
      G D.xFGroups.sequence D.cFGroups.sequence :=
  D.inclusion.toProfiniteFundamentalGroupInclusion

#check GroupsInclusion
#check GroupsInclusion.toProfiniteFundamentalGroupInclusion
#check CoreGroupsInput
#check CoreGroupsInput.fGroupInclusion
#print axioms GroupsInclusion.toProfiniteFundamentalGroupInclusion
#print axioms CoreGroupsInput.fGroupInclusion

end LeanFormal.IUT.XiFPaper.S2884GroupsInclusionActual
end
