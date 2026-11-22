import Mathlib.FieldTheory.AlgebraicClosure
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmFunctoriality
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegralUnitMapActual
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits

universe uK
variable {K : Type uK} [NormedField K] [IsUltrametricDist K]

/-- The ring map from the valuation integers into the algebraic closure. -/
def integerUnitsRingHom : Integers K →+* AlgebraicClosure K :=
  (algebraMap K (AlgebraicClosure K)).comp (Subring.subtype (Integers K))

theorem integerUnitsRingHom_injective :
    Function.Injective (integerUnitsRingHom (K := K)) := by
  intro x y h
  apply Subtype.ext
  apply (algebraMap K (AlgebraicClosure K)).injective
  simpa [integerUnitsRingHom] using h

/-- Actual map from integral units to algebraic-closure units. -/
def integersUnitsToAlgClosure : (Integers K)ˣ →* (AlgebraicClosure K)ˣ :=
  Units.map (integerUnitsRingHom (K := K)).toMonoidHom

theorem integersUnitsToAlgClosure_val (u : (Integers K)ˣ) :
    ((integersUnitsToAlgClosure (K := K) u : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
      algebraMap K (AlgebraicClosure K) (u : K) := rfl

theorem integersUnitsToAlgClosure_injective :
    Function.Injective (integersUnitsToAlgClosure (K := K)) :=
  Units.map_injective (integerUnitsRingHom_injective (K := K))

structure IntegralUnitToAlgClosureMap where
  map : (Integers K)ˣ →* (AlgebraicClosure K)ˣ
  injective : Function.Injective map

noncomputable def actualIntegralUnitToAlgClosureMap :
    IntegralUnitToAlgClosureMap (K := K) where
  map := integersUnitsToAlgClosure (K := K)
  injective := integersUnitsToAlgClosure_injective (K := K)

#print axioms integersUnitsToAlgClosure_injective
#print axioms actualIntegralUnitToAlgClosureMap
#print axioms integerUnitsRingHom_injective
#print axioms integersUnitsToAlgClosure_injective
end LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegralUnitMapActual