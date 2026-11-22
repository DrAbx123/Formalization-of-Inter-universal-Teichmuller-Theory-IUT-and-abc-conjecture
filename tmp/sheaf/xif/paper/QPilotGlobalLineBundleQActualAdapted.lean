import tmp.sheaf.xif.paper.QPilotGlobalLineBundleActual
import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamily
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelDivisor

/-! # Actual q-pilot global line bundle from the q_v multiplicities

QPilotGlobalLineBundleActual constructs the global ideal/line bundle with
exponent one at each base bad place.  The actual q_v zero locus has
multiplicity qVEffectiveMultiplicity (q_v order times the relative residue
degree).  This file constructs the corrected actual global ideal

  prod_b (m_b.maximalIdeal.asIdeal) ^ multiplicity_b,

its inverse fractional-ideal line bundle O(-D), the corresponding actual
GlobalIdealFamily, and the actual model-Frobenioid Object.  It proves the line
bundle's divisor class is the negative of qPilotQGlobalObject.divisorClass,
the actual equality corresponding to O(-D).

No inequality is asserted.  No toy/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.QPilotGlobalLineBundleQActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLineBundleActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The corrected global q-pilot ideal with actual q_v multiplicities. -/
noncomputable def qPilotQGlobalIdeal
    [Fintype (Bad (nativePlaceSelection X.S))] :
    Ideal (NumberField.RingOfIntegers (BaseField X)) :=
  ∏ b : Bad (nativePlaceSelection X.S),
    b.1.maximalIdeal.asIdeal ^ qVEffectiveMultiplicity X b

/-- The corrected global q-pilot fractional-ideal line bundle O(-D). -/
noncomputable def qPilotQGlobalLineBundle
    [Fintype (Bad (nativePlaceSelection X.S))] :
    FractionalIdeal
      (nonZeroDivisors (NumberField.RingOfIntegers (BaseField X)))
      (BaseField X) :=
  (qPilotQGlobalIdeal X : FractionalIdeal
    (nonZeroDivisors (NumberField.RingOfIntegers (BaseField X)))
    (BaseField X))⁻¹

/-- The line bundle is exactly the inverse of the corrected zero-locus ideal. -/
theorem qPilotQGlobalLineBundle_eq_inv_ideal
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotQGlobalLineBundle X =
      (qPilotQGlobalIdeal X : FractionalIdeal
        (nonZeroDivisors (NumberField.RingOfIntegers (BaseField X)))
        (BaseField X))⁻¹ := rfl

/-- The actual GlobalIdealFamily of the line bundle O(-D): finite coordinates
are the negative q_v multiplicities, archimedean coordinates are zero. -/
noncomputable def qPilotQGlobalLineBundleFamily
    [Fintype (Bad (nativePlaceSelection X.S))] :
    GlobalIdealFamily (BaseField X) where
  finite := -∑ b : Bad (nativePlaceSelection X.S),
    Finsupp.single (NumberFieldFinitePlace.underlyingPrime b.1)
      (qVEffectiveMultiplicity X b : Int)
  infinite := 0

/-- The actual model-Frobenioid Object of the q-pilot line bundle. -/
noncomputable def qPilotQGlobalLineBundleObject
    [Fintype (Bad (nativePlaceSelection X.S))] :
    Iut.SourceModelFrobenioid.Object
      (presentationDivisorMonoid (X := X)) :=
  objectOfIdealFamily (F := BaseField X) (qPilotQGlobalLineBundleFamily X)

/-- The line-bundle object's divisor class is the actual ideal-family divisor
class of O(-D). -/
theorem qPilotQGlobalLineBundleObject_divisorClass
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotQGlobalLineBundleObject X).divisorClass =
      idealFamilyDivisorClass (F := BaseField X)
        (qPilotQGlobalLineBundleFamily X) := rfl

/-- The zero-locus effective divisor is the negative of the line-bundle finite
family; this is the actual source sign for O(-D). -/
theorem qVZeroLocusQEffectiveGlobal_eq_neg_lineBundleFamily_finite
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotQGlobalLineBundleFamily X).finite =
      -∑ b : Bad (nativePlaceSelection X.S),
        Finsupp.single (NumberFieldFinitePlace.underlyingPrime b.1)
          (qVEffectiveMultiplicity X b : Int) := rfl

/-- The actual divisor-class equality corresponding to O(-D):
the line bundle class is the negative of the q-pilot effective divisor class. -/
theorem qPilotQGlobalLineBundleObject_divisorClass_eq_neg
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotQGlobalLineBundleObject X).divisorClass =
      - (qPilotQGlobalObject X).divisorClass := by
  rw [qPilotQGlobalLineBundleObject_divisorClass,
    qPilotQGlobalObject_divisorClass, idealFamilyDivisorClass]
  congr 1
  · ext v
    simp [qPilotQGlobalLineBundleFamily, qVZeroLocusQEffectiveGlobal,
      qVZeroLocusQEffectiveDivisor, Finsupp.neg_apply, Finset.sum_apply]
  · funext w
    simp [qPilotQGlobalLineBundleFamily]

/-- The corrected line bundle and the actual q-pilot object share the same
q_v/zero-locus data: the line bundle is O(-D) for the effective divisor D of
qPilotQGlobalObject. -/
theorem qPilotQGlobalLineBundleObject_link
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotQGlobalLineBundleObject X).divisorClass =
        - (qPilotQGlobalObject X).divisorClass ∧
      qPilotQGlobalLineBundle X =
        (qPilotQGlobalIdeal X : FractionalIdeal
          (nonZeroDivisors (NumberField.RingOfIntegers (BaseField X)))
          (BaseField X))⁻¹ :=
  ⟨qPilotQGlobalLineBundleObject_divisorClass_eq_neg X,
    qPilotQGlobalLineBundle_eq_inv_ideal X⟩

/-- Symmetric actual relation: the q-pilot presentation object's divisor class
is the negative of the line-bundle object's divisor class. -/
theorem qPilotQGlobalObject_divisorClass_eq_neg_lineBundle
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotQGlobalObject X).divisorClass =
      - (qPilotQGlobalLineBundleObject X).divisorClass := by
  rw [qPilotQGlobalLineBundleObject_divisorClass_eq_neg X]
  abel

/-- Actual relation between the q-pilot effective divisor and the line-bundle
family: the line-bundle finite coordinates are the negative multiplicities of
the zero-locus effective divisor. -/
theorem qPilotQGlobalLineBundle_family_relation
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotQGlobalLineBundleFamily X).finite =
      -∑ b : Bad (nativePlaceSelection X.S),
        Finsupp.single (NumberFieldFinitePlace.underlyingPrime b.1)
          (qVEffectiveMultiplicity X b : Int) := rfl

end LeanFormal.IUT.XiFPaper.QPilotGlobalLineBundleQActualAdapted

end
