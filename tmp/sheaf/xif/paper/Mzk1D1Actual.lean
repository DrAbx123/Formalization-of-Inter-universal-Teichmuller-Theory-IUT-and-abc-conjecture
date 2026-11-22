import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitGaloisDescent
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData

noncomputable section
namespace LeanFormal.IUT.XiFPaper.D1Actual

open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule

variable {K L : Type*} [NormedField K] [NormedField L] [NormedAlgebra K L]
variable [IsUltrametricDist K] [IsUltrametricDist L]
variable {p : Nat} [Fact p.Prime] [NormedAlgebra ℚ_[p] K] [NormedAlgebra ℚ_[p] L]
variable [IsScalarTower ℚ_[p] K L] [Algebra.IsAlgebraic ℚ_[p] L] [IsGalois K L]

abbrev fixedDegreeZeroUnits :=
  localGaloisFixedIntegralUnits (K := K) (L := L) (p := p)

def fixed_degreeZero_units_equiv :
    (Integers K)ˣ ≃* fixedDegreeZeroUnits (K := K) (L := L) (p := p) :=
  baseUnitsGaloisFixedEquiv (K := K) (L := L) (p := p)

def fixedDegreeZeroToNormOne :
    fixedDegreeZeroUnits (K := K) (L := L) (p := p) -> {x : L | ‖x‖ = 1} :=
  fun u => unitsNormOneHomeomorph (K := L) u.val

theorem fixedDegreeZeroToNormOne_apply
    (u : fixedDegreeZeroUnits (K := K) (L := L) (p := p)) :
    fixedDegreeZeroToNormOne (p := p) u = (u.val.val : L) := rfl

def capsuleInclusion {l : PrimeGeFive} {j j' : Nat} (h : j <= j') :
    Capsule j -> Capsule j' :=
  fun i => ⟨i.1, lt_of_lt_of_le i.2 (Nat.succ_le_succ h)⟩

theorem capsuleInclusion_square {l : PrimeGeFive} {j j' j'' : Nat}
    (h1 : j <= j') (h2 : j' <= j'') :
    capsuleInclusion (l := l) (le_trans h1 h2) =
      (capsuleInclusion (l := l) h2) ∘ (capsuleInclusion (l := l) h1) := by
  funext i
  apply Fin.ext
  rfl

end LeanFormal.IUT.XiFPaper.D1Actual
end
