import tmp.sheaf.xif.paper.Mzk1DLineBundleInterfaceConsumerActual
import tmp.sheaf.xif.paper.Mzk1DJointGreenConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D line-bundle cluster; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DLineBundleClusterActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleJointGenericActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleZeroDatumJointGenericActual
open LeanFormal.IUT.XiFPaper.Mzk1DLineBundleInterfaceConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1DJointGreenConsumerActual

universe u v w q

variable {R : Type u} [CommRing R] {X' : Type v} {A : Type w} [CommRing A] [Algebra R A]
  {F' : Type q} [Field F'] [Algebra R F']
  {U : Set X'} {f : A} {basicOpen : Set X'} {P' : Type*} {ord : P' → F' → ℤ}

theorem dLineBundleCluster_bundle (L : LineBundlePullbackInterface R A F') :
    Module.finrank R L.functionFieldSections = L.m :=
  dLineBundleInterfaceConsumer_finrank L

theorem dLineBundleCluster_joint (B : FibreBridgeAbstract X' A F' U f basicOpen P' ord)
    (L : LineBundlePullbackInterface R A F') (J : LineBundleZeroDatumJointGeneric B L) :
    (({t : X' | t ∈ U ∧ t ∉ basicOpen} : Set X') = B.placePoint '' (J.datum.T : Set P')) :=
  (dJointGreen_bundle B L J).1

def dLineBundleClusterRows : List (String × String × String) :=
  [ ("finrank = m", "PROVED", "dLineBundleCluster_bundle"),
    ("zero locus", "PROVED", "dLineBundleCluster_joint") ]

theorem dLineBundleClusterRows_length : dLineBundleClusterRows.length = 2 := rfl

#check dLineBundleCluster_bundle
#check dLineBundleClusterRows_length

end LeanFormal.IUT.XiFPaper.Mzk1DLineBundleClusterActual
end