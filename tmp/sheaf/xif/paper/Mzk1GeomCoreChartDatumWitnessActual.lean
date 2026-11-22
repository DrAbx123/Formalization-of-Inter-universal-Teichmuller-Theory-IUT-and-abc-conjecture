import tmp.sheaf.xif.paper.Mzk1GeomCoreChartWitnessActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreZeroDatumFibreActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: chart+datum witness (DAG foundation:D.finiteMapChart + D.zeroDatumFibre) -> FiniteMapChartData/FiniteMapChartData.toFiniteMapData + chart_fibreOverZeroEq (chart witness file) + fibreOverZeroEq_of_zeroDatum/restatedWitness (zero-datum fibre file) -> PROVED: chart + bridge + zero-divisor datum + degree/unramified/pullback => restated precise witness with T = datum-T image. Named: chart construction, bridge maps, actual sheaf. No closure.

# Mzk1GeomCoreChartDatumWitnessActual — chart + zero-datum => restated precise witness

PROVED:
* `chartDatum_fibre`: fibre condition from chart + bridge + datum;
* `chartDatum_restatedWitness`: restated precise witness;
* `chartDatum_recast`: old recast.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartDatumWitnessActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.SchemeLayer
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreZeroDatumFibreActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

/-- **PROVED:** chart + bridge + datum gives the fibre condition with datum T. -/
theorem chartDatum_fibre (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord)
    (Z : ZeroDivisorDatum P F ord) (hT : Z.T = B.Tplaces) :
    FibreOverZeroEq c ε X.toFiniteMapData (B.placePoint '' (Z.T : Set P)) :=
  fibreOverZeroEq_of_zeroDatum ord X.toFiniteMapData B Z hT

/-- **PROVED (conditional):** chart + bridge + datum + degree/unramified/pullback
=> restated precise witness. -/
def chartDatum_restatedWitness (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (hdeg : 0 < X.m)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord)
    (Z : ZeroDivisorDatum P F ord) (hT : Z.T = B.Tplaces)
    (D : Set C) (hunram : UnramifiedOverZero c ε X.toFiniteMapData)
    (hpull : PullbackIsoDegree c ε X.toFiniteMapData D) :
    Mzk1GeometricCoreWitnessPreciseRestated c ε
      (B.placePoint '' (Z.T : Set P)) D :=
  restatedWitness_of_data c ε _ D X.toFiniteMapData hdeg
    (chartDatum_fibre ord X B Z hT) hunram hpull

/-- **PROVED (conditional):** old recast. -/
theorem chartDatum_recast (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (hdeg : 0 < X.m)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord)
    (Z : ZeroDivisorDatum P F ord) (hT : Z.T = B.Tplaces)
    (D : Set C) (hunram : UnramifiedOverZero c ε X.toFiniteMapData)
    (hpull : PullbackIsoDegree c ε X.toFiniteMapData D) :
    Mzk1GeometricCoreRecast c ε (B.placePoint '' (Z.T : Set P)) D :=
  recast_of_restated ⟨chartDatum_restatedWitness ord X hdeg B Z hT D hunram hpull⟩

/-- Rows. -/
def chartDatumRows : List (String × String × String) :=
  [ ("chart + bridge + datum => fibre", "PROVED", "chartDatum_fibre")
  , ("chart + bridge + datum => restated witness", "PROVED (conditional)", "chartDatum_restatedWitness")
  , ("chart + bridge + datum => old recast", "PROVED (conditional)", "chartDatum_recast")
  , ("chart fields construction", "NAMED GAP", "finiteMapChartGapText")
  , ("bridge maps", "NAMED API GAP", "sectionMap/placePoint")
  , ("actual O(D) sheaf/psi^*", "NAMED GAP", "no Cartier/line-bundle API") ]

theorem chartDatumRows_length : chartDatumRows.length = 6 := rfl

#check chartDatum_fibre
#check chartDatum_restatedWitness
#check chartDatum_recast
#check chartDatumRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartDatumWitnessActual
end