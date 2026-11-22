import tmp.sheaf.xif.paper.Mzk1GeomCoreLineBundleJointGenericActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreZeroDatumFibreActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: generic zero-datum + line-bundle joint -> LineBundleBridgeJoint (generic joint) + ZeroDivisorDatum/FibreBridgeAbstract/zeroSet_eq_of_abstract -> PROVED generic: zero locus of f in U equals placePoint '' datum.T; order one at T; degree. No closure.

# Mzk1GeomCoreLineBundleZeroDatumJointGenericActual — generic zero-datum/line-bundle joint

PROVED:
* `LineBundleZeroDatumJointGeneric`;
* `jointZD_zeroLocus`: {t in U : t notin basicOpen} = placePoint '' datum.T;
* `jointZD_order_pos`, `jointZD_datum_order`, `jointZD_degree`.
NAMED: actual O(D)/psi^*, bridge maps.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleZeroDatumJointGenericActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleJointGenericActual

universe u v w q

variable {R : Type u} [CommRing R] {X : Type v} {A : Type w} [CommRing A] [Algebra R A]
  {F : Type q} [Field F] [Algebra R F]
  {U : Set X} {f : A} {basicOpen : Set X} {P : Type*} {ord : P → F → ℤ}

/-- Generic zero-divisor datum + line-bundle joint. -/
structure LineBundleZeroDatumJointGeneric
    (B : FibreBridgeAbstract X A F U f basicOpen P ord)
    (L : LineBundlePullbackInterface R A F) where
  joint : LineBundleBridgeJoint B L
  datum : ZeroDivisorDatum P F ord
  T_eq : datum.T = B.Tplaces

/-- **PROVED:** zero locus of f in U equals the datum-T image. -/
theorem jointZD_zeroLocus (B : FibreBridgeAbstract X A F U f basicOpen P ord)
    (L : LineBundlePullbackInterface R A F) (J : LineBundleZeroDatumJointGeneric B L) :
    ({t : X | t ∈ U ∧ t ∉ basicOpen} : Set X) = B.placePoint '' (J.datum.T : Set P) := by
  rw [zeroSet_eq_of_abstract B, J.T_eq]

/-- **PROVED:** order positivity of the section image at datum-T. -/
theorem jointZD_order_pos (B : FibreBridgeAbstract X A F U f basicOpen P ord)
    (L : LineBundlePullbackInterface R A F) (J : LineBundleZeroDatumJointGeneric B L)
    (p : P) (hp : p ∈ J.datum.T) :
    0 < ord p (L.iso ⟨L.f, L.f_mem⟩ : F) := by
  apply Tplaces_order_pos J.joint.compatibility p
  rw [← J.T_eq]
  exact hp

/-- **PROVED:** datum order one at T. -/
theorem jointZD_datum_order (B : FibreBridgeAbstract X A F U f basicOpen P ord)
    (L : LineBundlePullbackInterface R A F) (J : LineBundleZeroDatumJointGeneric B L)
    (p : P) (hp : p ∈ J.datum.T) : ord p J.datum.g = 1 :=
  J.datum.zero_simple p hp

/-- **PROVED:** degree equals function-field section rank. -/
theorem jointZD_degree (B : FibreBridgeAbstract X A F U f basicOpen P ord)
    (L : LineBundlePullbackInterface R A F) (J : LineBundleZeroDatumJointGeneric B L) :
    Module.finrank R L.functionFieldSections = L.m :=
  finrank_functionFieldSections_eq L

def jointZDRows : List (String × String × String) :=
  [ ("zero locus identification", "PROVED", "jointZD_zeroLocus")
  , ("order positivity", "PROVED", "jointZD_order_pos")
  , ("datum order one", "PROVED", "jointZD_datum_order")
  , ("degree", "PROVED", "jointZD_degree")
  , ("actual O(D)/psi^*", "NAMED", "no Cartier/line-bundle API") ]

theorem jointZDRows_length : jointZDRows.length = 5 := rfl

#check jointZD_zeroLocus
#check jointZD_order_pos
#check jointZD_degree
#check jointZDRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleZeroDatumJointGenericActual
end