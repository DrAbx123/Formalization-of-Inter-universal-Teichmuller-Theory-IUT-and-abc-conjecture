import tmp.sheaf.xif.paper.Mzk1Ind1IntegrationActionActual
import tmp.sheaf.xif.paper.Mzk1Ind1ActualSourceUnitLayerActual
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralActionActual
open LeanFormal.IUT LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegrationActionActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1ActualSourceUnitLayerActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegralUnitMapActual

variable {p : Nat} [Fact p.Prime]

/-- The local Galois action fixes every integral unit embedded in the
algebraic closure, because those elements lie in the image of `ℚ_[p]`. -/
theorem localGaloisUnitsAction_fixes_integralUnits
    (σ : LeanFormal.IUT.LocalAbsoluteGalois p) (u : (Integers ℚ_[p])ˣ) :
    localGaloisUnitsAction p σ (integersUnitsToAlgClosure (K := ℚ_[p]) u) =
      integersUnitsToAlgClosure (K := ℚ_[p]) u := by
  apply Units.ext
  change σ (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) (u : ℚ_[p])) =
    algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) (u : ℚ_[p])
  exact σ.commutes (u : ℚ_[p])

/-- The actual stable action from an element of the local absolute Galois
group.  It fixes the integral-unit image pointwise. -/
def localGaloisStableAlgebraicAction (σ : LeanFormal.IUT.LocalAbsoluteGalois p) :
    IntegralUnitStableAlgebraicAction ℚ_[p] where
  algAction := localGaloisUnitsAction p σ
  mapsIntegers u := ⟨u, (localGaloisUnitsAction_fixes_integralUnits σ u).symm⟩
  mapsIntegers_symm u := ⟨u, (localGaloisUnitsAction_fixes_integralUnits σ.symm u).symm⟩

/-- The actual Ind1 unit action from a local absolute Galois element.  On the
base field `ℚ_[p]` its integral-unit quotient action is the identity. -/
def localGaloisActualInd1UnitAction (σ : LeanFormal.IUT.LocalAbsoluteGalois p) :
    ActualInd1UnitAction ℚ_[p] where
  algAction := localGaloisUnitsAction p σ
  beta := MulEquiv.refl _
  compatible u := ⟨u, rfl, (localGaloisUnitsAction_fixes_integralUnits σ u).symm⟩

#print axioms localGaloisUnitsAction_fixes_integralUnits
#print axioms localGaloisActualInd1UnitAction
end LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralActionActual