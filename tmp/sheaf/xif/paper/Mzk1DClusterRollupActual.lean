import tmp.sheaf.xif.paper.Mzk1GeomCoreChartDatumWitnessActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreLineBundleZeroDatumJointGenericActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreChartBasicFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D cluster rollup; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DClusterRollupActual

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
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartDatumWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartBasicFactsActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

theorem dClusterRollup_chart (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m ∧ ((X.toFiniteMapData.U : Set C) = (Set.range ε.1.base)ᶜ) :=
  ⟨chartBasic_m X, chartBasic_U X⟩

theorem dClusterRollup_generic {X' : Type*} {A : Type*} [CommRing A] [Algebra R A]
    {F' : Type*} [Field F'] [Algebra R F']
    {U : Set X'} {f : A} {basicOpen : Set X'} {P' : Type*} {ord : P' → F' → ℤ}
    (B : FibreBridgeAbstract X' A F' U f basicOpen P' ord)
    (L : LineBundlePullbackInterface R A F') (J : LineBundleZeroDatumJointGeneric B L) :
    ({t : X' | t ∈ U ∧ t ∉ basicOpen} : Set X') = B.placePoint '' (J.datum.T : Set P') :=
  jointZD_zeroLocus B L J

def dClusterRollupRows : List (String × String × String) :=
  [ ("chart basic identity", "PROVED", "dClusterRollup_chart"),
    ("generic zero locus", "PROVED", "dClusterRollup_generic") ]

theorem dClusterRollupRows_length : dClusterRollupRows.length = 2 := rfl

#check dClusterRollup_chart
#check dClusterRollupRows_length

end LeanFormal.IUT.XiFPaper.Mzk1DClusterRollupActual
end