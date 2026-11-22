import tmp.sheaf.xif.paper.S2434D9AttackActual
import Mathlib.CategoryTheory.Sites.Over

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2103D9PrestackActual
open LeanFormal.IUT.XiFPaper.S2434D9AttackActual
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2436SlicePushProofActual

universe v u v' u'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

-- Exact reduced goal after ext phi, change, and unfolding slicePush/pullHom:
--
-- ((unop X2).iteratedSliceEquiv.inverse.sheafPushforwardContinuous ...).map
--   (((J.over S).overMapPullback A f.unop).map phi)
-- =
-- ((J.pseudofunctorOver A).mapComp' ...).hom.toNatTrans.app M
--   ≫ ((J.pseudofunctorOver A).map (p.left).op.toLoc).toFunctor.map
--       ((slicePush X1).map phi)
--   ≫ ((J.pseudofunctorOver A).mapComp' ...).inv.toNatTrans.app N
--
-- This is the exact pullHom coherence missing.  It is the comparison between
-- Over.overMapPullback and the pseudofunctor mapComp' built from Over.mapComp,
-- mediated by Over.iteratedSliceEquivOverMapIso.  No proof was completed.
#check S2434SlicePush_iff_pullHom
#check Over.iteratedSliceEquivOverMapIso
#check Pseudofunctor.LocallyDiscreteOpToCat.pullHom

end LeanFormal.IUT.XiFPaper.S2436SlicePushProofActual

end
