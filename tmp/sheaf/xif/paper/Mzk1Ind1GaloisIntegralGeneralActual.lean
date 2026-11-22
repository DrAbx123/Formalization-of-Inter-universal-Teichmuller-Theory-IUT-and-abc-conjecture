import tmp.sheaf.xif.paper.Mzk1Ind1IntegrationActionActual
import tmp.sheaf.xif.paper.Mzk1Ind1ActualSourceUnitLayerActual
import tmp.sheaf.xif.paper.Mzk1Ind1IntegralUnitMapActual
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralGeneralActual
open LeanFormal.IUT LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegrationActionActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1ActualSourceUnitLayerActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegralUnitMapActual

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/-- Unit action on the algebraic closure induced by a `K`-algebra automorphism. -/
def localUnitsAction (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    MulAut (AlgebraicClosure K)ˣ :=
  Units.mapEquiv σ.toRingEquiv.toMulEquiv

/-- A `K`-algebra automorphism of the algebraic closure fixes the embedded
integral units pointwise, because it fixes `K` pointwise. -/
theorem localUnitsAction_fixes_integralUnits
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (u : (Integers K)ˣ) :
    localUnitsAction σ (integersUnitsToAlgClosure (K := K) u) =
      integersUnitsToAlgClosure (K := K) u := by
  apply Units.ext
  change σ (algebraMap K (AlgebraicClosure K) (u : K)) =
    algebraMap K (AlgebraicClosure K) (u : K)
  exact σ.commutes (u : K)

def localStableAlgebraicAction
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    IntegralUnitStableAlgebraicAction K where
  algAction := localUnitsAction σ
  mapsIntegers u := ⟨u, (localUnitsAction_fixes_integralUnits σ u).symm⟩
  mapsIntegers_symm u := ⟨u, (localUnitsAction_fixes_integralUnits σ.symm u).symm⟩

def localActualInd1UnitAction
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    ActualInd1UnitAction K where
  algAction := localUnitsAction σ
  beta := MulEquiv.refl _
  compatible u := ⟨u, rfl, (localUnitsAction_fixes_integralUnits σ u).symm⟩

#print axioms localUnitsAction_fixes_integralUnits
#print axioms localActualInd1UnitAction
end LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralGeneralActual