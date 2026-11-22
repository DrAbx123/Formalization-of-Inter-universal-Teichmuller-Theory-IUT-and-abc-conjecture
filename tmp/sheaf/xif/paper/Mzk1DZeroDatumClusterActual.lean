import tmp.sheaf.xif.paper.Mzk1GeomCoreZeroDatumFibreActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreLineBundleZeroDatumJointGenericActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D zero-datum cluster; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DZeroDatumClusterActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.SchemeLayer
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleJointGenericActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleZeroDatumJointGenericActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

theorem dZeroDatumCluster_generic {X' : Type*} {A : Type*} [CommRing A] [Algebra R A]
    {F' : Type*} [Field F'] [Algebra R F']
    {U : Set X'} {f : A} {basicOpen : Set X'} {P' : Type*} {ord : P' → F' → ℤ}
    (B : FibreBridgeAbstract X' A F' U f basicOpen P' ord)
    (L : LineBundlePullbackInterface R A F') (J : LineBundleZeroDatumJointGeneric B L) :
    ({t : X' | t ∈ U ∧ t ∉ basicOpen} : Set X') = B.placePoint '' (J.datum.T : Set P') :=
  jointZD_zeroLocus B L J

def dZeroDatumClusterRows : List (String × String × String) :=
  [ ("generic zero locus", "PROVED", "dZeroDatumCluster_generic") ]

theorem dZeroDatumClusterRows_length : dZeroDatumClusterRows.length = 1 := rfl

#check dZeroDatumCluster_generic
#check dZeroDatumClusterRows_length

end LeanFormal.IUT.XiFPaper.Mzk1DZeroDatumClusterActual
end