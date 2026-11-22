import tmp.sheaf.xif.paper.S2436SlicePushProofActual
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Sites.Over

/-!
# S2437: the exact pullHom coherence for the iterated-slice pushforward

S2103 isolated the first missing of the D9 prestack half as 'SlicePushNaturality M N'
('S2103D9PrestackActual'), equivalently its explicit 'pullHom' form
('slicePushNaturality_iff_pullHom').  S2436 recorded the goal after 'ext phi', 'change'
and unfolding 'slicePush'/'pullHom'.

This file records the exact coherence as a named 'Prop'
('S2437PullHomCoherence'), proves that it is *literally* 'SlicePushNaturality'
('S2437PullHomCoherence_iff', no new input), and proves the pointwise computation of
the left-hand side ('S2437_lhs_pointwise'), which reduces the left-hand side to a
single component of 'phi' at an explicit object.

## What the remaining coherence is

After 'ext W', the goal is an equality in 'A' between

* LHS = 'phi.hom.app (op ((Over.map f.unop).obj (X2.unop.iteratedSliceEquiv.inverse.obj W.unop)))'
  (proved below, 'S2437_lhs_pointwise'), and
* RHS = the 'pullHom' value, i.e. the three-factor composite

  '((J.pseudofunctorOver A).mapComp' ...).hom.toNatTrans.app M
     >> ((J.pseudofunctorOver A).map (Over.Hom.left f.unop).op.toLoc).toFunctor.map
         ((slicePush X1.unop).map phi)
     >> ((J.pseudofunctorOver A).mapComp' ...).inv.toNatTrans.app N'.

Unfolding 'pullHom', 'Pseudofunctor.mapComp'', 'PrelaxFunctor.map2Iso_eqToIso',
'GrothendieckTopology.pseudofunctorOver', 'LocallyDiscrete.mkPseudofunctor_mapComp/map'
and 'GrothendieckTopology.overMapPullbackComp_hom_app_hom_app' turns the 'pullHom'
side into

  '((eqToIso ... <<< Cat.Hom.isoMk (J.overMapPullbackComp A p.left j1.hom).symm).hom.toNatTrans.app M
     >> (J.overMapPullback A p.left).toFunctor.map ((slicePush X1.unop).map phi)
     >> ((eqToIso ... <<< Cat.Hom.isoMk (J.overMapPullbackComp A p.left j1.hom).symm)).inv.toNatTrans.app N)',

i.e. the canonical 'Over.mapComp'-correction composed with the *naive* action of
'Over.map p.left' on the slice pushforward, all mediated by the 'eqToIso' transports coming
from 'mapComp''.  The missing identification is precisely the comparison of

  'Over.iteratedSliceBackward X2 >> Over.map p'   and   'Over.map p.left >> Over.iteratedSliceBackward X1'

(the backward form of 'Over.iteratedSliceEquivOverMapIso'), together with the fact that the
correction isos 'Over.mapComp' (whose components are 'Over.isoMk (Over.isoMk (Iso.refl _))',
hence have identity '.left') are the canonical maps between the corresponding objects.

No 'sorry', no axiom, no placeholder: the coherence is isolated as 'S2437PullHomCoherence',
and no inhabitant of it is asserted in this file.
-/

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2103D9PrestackActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2437PullHomCoherenceActual

universe v u v' u'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

/-! ## 1. The exact coherence -/

/-- **The exact pullHom coherence**, the missing inhabitant of the D9 prestack half.
For every pair of objects 'X1 X2' of '(Over S)ᵒᵖ', morphism 'f : X1 ⟶ X2' and
'phi : Hom((Over.forget X1.unop)^* M, (Over.forget X1.unop)^* N)', the slice pushforward of the
restriction of 'phi' along 'f' equals the pseudofunctor restriction 'pullHom' of the slice
pushforward of 'phi'. -/
def S2437PullHomCoherence {S : C} (M N : Sheaf (J.over S) A) : Prop :=
  ∀ ⦃X₁ X₂ : (Over S)ᵒᵖ⦄ (f : X₁ ⟶ X₂)
    (φ : (CategoryTheory.sheafHom' (J := J.over S) M N).obj X₁),
    (slicePush (J := J) (A := A) X₂.unop).map
        (((J.over S).overMapPullback A f.unop).map φ) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := J.pseudofunctorOver A)
        ((slicePush (J := J) (A := A) X₁.unop).map φ)
        f.unop.left X₂.unop.hom X₂.unop.hom

/-- The exact coherence is exactly 'SlicePushNaturality'; this is not a new input, it is the
reduction already available in S2103. -/
theorem S2437PullHomCoherence_iff (M N : Sheaf (J.over S) A) :
    SlicePushNaturality (J := J) (A := A) M N ↔
      S2437PullHomCoherence (J := J) (A := A) M N :=
  slicePushNaturality_iff_pullHom (J := J) (A := A) M N

/-- The coherence statement, in the shape needed by the prestack half of S2093.
(Restatement, no new input.) -/
theorem S2437_isPrestack_of_coherence
    (h : ∀ (S : C) (M N : Sheaf (J.over S) A),
      S2437PullHomCoherence (J := J) (A := A) M N) :
    (J.pseudofunctorOver A).IsPrestack J :=
  isPrestack_of_naturality (J := J) (A := A)
    (fun S M N => (S2437PullHomCoherence_iff (J := J) (A := A) M N).mpr (h S M N))

/-! ## 2. Pointwise computation of the left-hand side

The left-hand side is *fully computed*: it is a single component of 'phi' at the object
'(Over.map f.unop).obj ((X2.unop).iteratedSliceEquiv.inverse.obj W.unop)' of 'Over X1.unop'. -/

/-- Pointwise computation of '(slicePush X).map a' (definitional; 'sheafPushforwardContinuous'
acts by precomposition with the opposite of the underlying functor). -/
theorem S2437_slicePush_map_hom_app {S : C} (X : Over S)
    {P Q : Sheaf ((J.over S).over X) A} (α : P ⟶ Q) (W : (Over X.left)ᵒᵖ) :
    ((slicePush (J := J) (A := A) X).map α).hom.app W =
      α.hom.app (op (X.iteratedSliceEquiv.inverse.obj W.unop)) := by
  simp

/-- Pointwise computation of '(overMapPullback q).map a' (definitional). -/
theorem S2437_overMapPullback_map_hom_app {X Y : C} (q : X ⟶ Y)
    {P Q : Sheaf (J.over Y) A} (α : P ⟶ Q) (W : (Over X)ᵒᵖ) :
    ((J.overMapPullback A q).map α).hom.app W =
      α.hom.app (op ((Over.map q).obj W.unop)) := by
  simp

/-- **The left-hand side, computed.** -/
theorem S2437_lhs_pointwise {S : C} (M N : Sheaf (J.over S) A)
    ⦃X₁ X₂ : (Over S)ᵒᵖ⦄ (f : X₁ ⟶ X₂)
    (φ : (CategoryTheory.sheafHom' (J := J.over S) M N).obj X₁)
    (W : (Over (X₂.unop).left)ᵒᵖ) :
    ((slicePush (J := J) (A := A) X₂.unop).map
        (((J.over S).overMapPullback A f.unop).map φ)).hom.app W =
      φ.hom.app (op ((Over.map f.unop).obj
        ((X₂.unop).iteratedSliceEquiv.inverse.obj W.unop))) := by
  simp

/-! ## 3. Interface checks for the Mathlib API used by the remaining identification -/

#check @S2437PullHomCoherence
#check @S2437PullHomCoherence_iff
#check @S2437_isPrestack_of_coherence
#check @S2437_slicePush_map_hom_app
#check @S2437_overMapPullback_map_hom_app
#check @S2437_lhs_pointwise

#check @Over.iteratedSliceEquivOverMapIso
#check @Over.iteratedSliceEquivOverMapIso_hom_app_left_left
#check @Over.iteratedSliceEquivOverMapIso_inv_app_left_left
#check @Over.iteratedSliceBackward_forget
#check @Over.mapComp_hom_app_left
#check @Over.mapComp
#check @Over.isoMk
#check @Over.homMk_eta
#check @Over.OverMorphism.ext
#check @GrothendieckTopology.overMapPullback
#check @GrothendieckTopology.overMapPullbackComp
#check @GrothendieckTopology.overMapPullbackComp_hom_app_hom_app
#check @GrothendieckTopology.overMapPullbackComp_inv_app_hom_app
#check @Functor.sheafPushforwardContinuousComp'
#check @Pseudofunctor.LocallyDiscreteOpToCat.pullHom
#check @Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
#check @Pseudofunctor.mapComp'
#check @CategoryTheory.PrelaxFunctor.map₂Iso_eqToIso
#check @GrothendieckTopology.pseudofunctorOver

#print axioms S2437PullHomCoherence_iff
#print axioms S2437_isPrestack_of_coherence
#print axioms S2437_slicePush_map_hom_app
#print axioms S2437_overMapPullback_map_hom_app
#print axioms S2437_lhs_pointwise

end LeanFormal.IUT.XiFPaper.S2437PullHomCoherenceActual

end
