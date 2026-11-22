import tmp.sheaf.xif.paper.Mzk1GeomCoreLineBundleBridgeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: generic line-bundle + bridge joint (DAG foundation:D.lineBundleBridge/D.chartBridgeLineBundle) -> LineBundlePullbackInterface + FibreBridgeAbstract + LineBundleOrderCompatibility -> PROVED generic joint facts: iso image, order transfer, degree; no chart/section-ring instance needed ([Algebra R A] explicit). No closure.

# Mzk1GeomCoreLineBundleJointGenericActual — generic line-bundle/bridge joint

PROVED:
* `LineBundleBridgeJoint`: bridge + line-bundle interface + compatibility;
* `jointGeneric_iso_image` / `jointGeneric_order_pos` / `jointGeneric_degree`.
NAMED: actual O(D) sheaf, psi^* pullback, bridge maps.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleJointGenericActual

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleBridgeActual

universe u v w q

variable {R : Type u} [CommRing R] {X : Type v} {A : Type w} [CommRing A] [Algebra R A]
  {F : Type q} [Field F] [Algebra R F]
  {U : Set X} {f : A} {basicOpen : Set X} {P : Type*} {ord : P → F → ℤ}

/-- Generic joint data. -/
structure LineBundleBridgeJoint
    (B : FibreBridgeAbstract X A F U f basicOpen P ord)
    (L : LineBundlePullbackInterface R A F) where
  compatibility : LineBundleOrderCompatibility B L

/-- **PROVED:** iso image of the distinguished section equals the bridge section. -/
theorem jointGeneric_iso_image (B : FibreBridgeAbstract X A F U f basicOpen P ord)
    (L : LineBundlePullbackInterface R A F) (J : LineBundleBridgeJoint B L) :
    (L.iso ⟨L.f, L.f_mem⟩ : F) = B.sectionMap f := by
  exact iso_image_f_eq_sectionMap J.compatibility

/-- **PROVED:** order/zero-locus transfer. -/
theorem jointGeneric_order_pos (B : FibreBridgeAbstract X A F U f basicOpen P ord)
    (L : LineBundlePullbackInterface R A F) (J : LineBundleBridgeJoint B L)
    (p : P) (hU : B.placePoint p ∈ U) :
    B.placePoint p ∉ basicOpen ↔ 0 < ord p (L.iso ⟨L.f, L.f_mem⟩ : F) :=
  order_pos_iff J.compatibility p hU

/-- **PROVED:** degree = function-field section rank. -/
theorem jointGeneric_degree (B : FibreBridgeAbstract X A F U f basicOpen P ord)
    (L : LineBundlePullbackInterface R A F) (J : LineBundleBridgeJoint B L) :
    Module.finrank R L.functionFieldSections = L.m :=
  finrank_functionFieldSections_eq L

def jointGenericRows : List (String × String × String) :=
  [ ("generic joint data", "DEFINED", "LineBundleBridgeJoint")
  , ("iso image", "PROVED", "jointGeneric_iso_image")
  , ("order transfer", "PROVED", "jointGeneric_order_pos")
  , ("degree", "PROVED", "jointGeneric_degree")
  , ("actual O(D)/psi^*", "NAMED", "no Cartier/line-bundle API") ]

theorem jointGenericRows_length : jointGenericRows.length = 5 := rfl

#check jointGeneric_iso_image
#check jointGeneric_order_pos
#check jointGeneric_degree
#check jointGenericRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleJointGenericActual
end