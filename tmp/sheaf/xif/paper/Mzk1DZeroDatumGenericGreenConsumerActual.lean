import tmp.sheaf.xif.paper.Mzk1GeomCoreLineBundleZeroDatumJointGenericActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D zero-datum generic green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DZeroDatumGenericGreenConsumerActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleJointGenericActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleZeroDatumJointGenericActual

universe u v w q

variable {R : Type u} [CommRing R] {X : Type v} {A : Type w} [CommRing A] [Algebra R A]
  {F : Type q} [Field F] [Algebra R F]
  {U : Set X} {f : A} {basicOpen : Set X} {P : Type*} {ord : P → F → ℤ}

theorem dZeroDatumGenericGreen_bundle (B : FibreBridgeAbstract X A F U f basicOpen P ord)
    (L : LineBundlePullbackInterface R A F) (J : LineBundleZeroDatumJointGeneric B L) :
    ({t : X | t ∈ U ∧ t ∉ basicOpen} : Set X) = B.placePoint '' (J.datum.T : Set P) ∧
      Module.finrank R L.functionFieldSections = L.m :=
  ⟨jointZD_zeroLocus B L J, jointZD_degree B L J⟩

def dZeroDatumGenericGreenRows : List (String × String × String) :=
  [ ("zero locus + degree bundle", "PROVED", "dZeroDatumGenericGreen_bundle") ]

theorem dZeroDatumGenericGreenRows_length : dZeroDatumGenericGreenRows.length = 1 := rfl

#check dZeroDatumGenericGreen_bundle
#check dZeroDatumGenericGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1DZeroDatumGenericGreenConsumerActual
end