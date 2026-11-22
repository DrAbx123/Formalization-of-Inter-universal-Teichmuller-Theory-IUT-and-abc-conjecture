import tmp.sheaf.xif.paper.Mzk1GeomCoreLineBundleJointGenericActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreZeroDatumFibreActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D line-bundle green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DLineBundleGreenConsumerActual

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

theorem dLineBundleGreen_bundle (B : FibreBridgeAbstract X A F U f basicOpen P ord)
    (L : LineBundlePullbackInterface R A F) (J : LineBundleBridgeJoint B L) :
    (L.iso ⟨L.f, L.f_mem⟩ : F) = B.sectionMap f ∧
      Module.finrank R L.functionFieldSections = L.m :=
  ⟨jointGeneric_iso_image B L J, jointGeneric_degree B L J⟩

def dLineBundleGreenRows : List (String × String × String) :=
  [ ("iso image + degree bundle", "PROVED", "dLineBundleGreen_bundle") ]

theorem dLineBundleGreenRows_length : dLineBundleGreenRows.length = 1 := rfl

#check dLineBundleGreen_bundle
#check dLineBundleGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1DLineBundleGreenConsumerActual
end