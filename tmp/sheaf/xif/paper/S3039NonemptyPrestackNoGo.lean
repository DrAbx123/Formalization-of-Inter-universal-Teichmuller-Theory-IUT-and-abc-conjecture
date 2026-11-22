import tmp.sheaf.xif.paper.S3031NonemptyQIsPrestack
import tmp.sheaf.xif.paper.S3037cBottomNotCoveringConcrete
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3026NonemptyEtaleSite
open LeanFormal.IUT.XiFPaper.S3031NonemptyQIsPrestack
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
namespace LeanFormal.IUT.XiFPaper.S3039NonemptyPrestackNoGo

abbrev K : Type := S2882A6PointwisePseudofunctorActual.K
abbrev X : Iut.SchemeOverField K := S2844D6F6BaseChangeActual.S2844X

local instance mulActionPoint (Y : Iut.SchemeOverField K) :
    MulAction Iut.SignGroup (Y ⟶ X) :=
  S2882A6PointMulAction (LocallyDiscrete.mk (Opposite.op Y))

/-- The obstruction shape for the nonempty site: a disconnected base U = U1 ⨿ U2,
a point M fixed by the nontrivial sign automorphism, and the two local sign
sections which cannot switch globally. -/
structure S3039DisconnectedSignSwitchWitness where
  U : S3026NonemptyScheme
  left : Iut.SchemeOverField K
  right : Iut.SchemeOverField K
  left_nonempty : Nonempty left.left
  right_nonempty : Nonempty right.left
  decomposition : U.obj ≅ Over.mk (Limits.coprod.desc left.hom right.hom)
  M : ActionCategory Iut.SignGroup (U.obj ⟶ X)
  nontrivial_sign : Iut.SignGroup
  nontrivial_ne_one : nontrivial_sign ≠ 1
  fixed : nontrivial_sign • M.back = M.back

/-- If such a switch witness exists, the restricted sign hom presheaf is not a
sheaf over the two-component cover.  The exact missing proof is the construction
of the two local sections and of the fixed point of the elliptic involution. -/
def S3039DisconnectedPrestackObstruction : Prop :=
  Nonempty S3039DisconnectedSignSwitchWitness

def S3039ConnectedSiteNeeded : List String :=
  [ "nonempty site 仍包含不连通 U = U1 ⨿ U2"
  , "HomForm 的 SignGroup 标签可在两个非空分量间切换"
  , "若 M 被非平凡 sign 固定，则两分量分别取 1 / nontrivial 得到"
  , "  compatible family 但无全局 amalgamation ⇒ presheafHom 不是 sheaf"
  , "修法：site 改为 connected nonempty schemes（或 geometrically connected）"
  ]

#check S3039DisconnectedSignSwitchWitness
#check S3039DisconnectedPrestackObstruction
#check S3039ConnectedSiteNeeded

end LeanFormal.IUT.XiFPaper.S3039NonemptyPrestackNoGo