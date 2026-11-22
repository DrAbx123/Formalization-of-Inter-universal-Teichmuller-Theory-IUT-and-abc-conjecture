import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmFunctoriality
import LeanFormal.IUT.Foundations.LocalFields.UnitPerfectionFunctoriality
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1LogLatticeActionActual
open LeanFormal.IUT LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped BigOperators

universe uF uL
variable {F : Type uF} [NormedField F] [IsUltrametricDist F]
variable {L : Type uL} [NormedField L] [IsUltrametricDist L]
variable [CharZero F] [CompleteSpace F] [ProperSpace F]
variable [CharZero L] [CompleteSpace L] [ProperSpace L]
variable {p : Nat} [Fact p.Prime]
variable [NormedAlgebra ℚ_[p] F] [NormedAlgebra ℚ_[p] L]
variable [Algebra.IsAlgebraic ℚ_[p] L]

/-- Single-place Ind1 action from an actual isometric field map: the actual
integral-unit map, its rationalized perfection map, the log square, and the
integral-log-shell preservation.  This is built from `integralUnitMap`
and `unitPerfectionMap`; it is not an arbitrary same-dimension equivalence. -/
structure SinglePlaceLogLatticeAction
    (F : Type uF) [NormedField F] [IsUltrametricDist F] [CharZero F]
    [CompleteSpace F] [ProperSpace F]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CharZero L]
    [CompleteSpace L] [ProperSpace L]
    (p : Nat) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] F] [NormedAlgebra ℚ_[p] L]
    [Algebra.IsAlgebraic ℚ_[p] L]
    (e : F →+* L) (he : Isometry e) where
  unitMap : (Integers F)ˣ →* (Integers L)ˣ
  unitMap_eq : unitMap = integralUnitMap e he
  perfectionMap : UnitLogPerfection F →ₗ[ℚ] UnitLogPerfection L
  perfectionMap_eq : perfectionMap = unitPerfectionMap e he
  logSquare : ∀ x : UnitLogPerfection F,
    algebraicUnitPerfectionEquiv (p := p) (perfectionMap x) =
      e (unitLogPerfectionEquiv (p := p) x)
  shellPreserve : ∀ x : F,
    x ∈ integralLogShell (K := F) (p := p) →
      e x ∈ integralLogShell (K := L) (p := p)

end LeanFormal.IUT.XiFPaper.Mzk1Ind1LogLatticeActionActual