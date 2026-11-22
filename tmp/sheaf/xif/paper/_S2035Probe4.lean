import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceGaloisLogShell
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitGaloisDescent
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import Mathlib.FieldTheory.KrullTopology

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm

namespace S2035Probe4

variable (v : FinitePrimePlace 2 7)
local instance : Fact (Nat.Prime v.1) := ⟨v.2.2.2⟩

abbrev QPlace (v : FinitePrimePlace 2 7) : NumberField.FinitePlace ℚ :=
  rationalFinitePlace v.1

abbrev Kv (v : FinitePrimePlace 2 7) : Type := NormalizedCompletion (QPlace v)
abbrev Lv (v : FinitePrimePlace 2 7) : Type := SourceAlgebraicClosure (QPlace v)
abbrev Gv (v : FinitePrimePlace 2 7) : Type := Lv v ≃ₐ[Kv v] Lv v

-- bridge from the FinitePlace completion to the height-one completion
noncomputable def completionBridge :
    Completion (QPlace v) ≃+* (rationalHeightOneSpectrum v.1).adicCompletion ℚ :=
  RingEquiv.cast (rationalFinitePlace_underlyingPrime v.1)

-- p-adic field equiv with normalized completion
noncomputable def completionPadicEquiv :
    ℚ_[v.1] ≃+* Kv v :=
  (rationalFinitePlacePadicEquiv v.1).toRingEquiv.trans
    ((completionBridge v).symm.trans (normalizedCompletionRingEquiv (QPlace v)).symm)

-- algebraic closure equiv
noncomputable def eAlgClosure :
    AlgebraicClosure ℚ_[v.1] ≃+* Lv v :=
  IsAlgClosure.equivOfEquiv (L := AlgebraicClosure ℚ_[v.1]) (M := Lv v)
    (S := ℚ_[v.1]) (R := Kv v) (completionPadicEquiv v)

example (x : ℚ_[v.1]) :
    eAlgClosure v (algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1]) x) =
      algebraMap (Kv v) (Lv v) (completionPadicEquiv v x) := by
  exact IsAlgClosure.equivOfEquiv_algebraMap _ _ _ x

-- integral fixed units
noncomputable def fixedIntegralUnits :
    (Integers (Kv v))ˣ ≃* localGaloisFixedIntegralUnits
      (K := Kv v) (L := Lv v) (p := (completionRationalPrime (QPlace v)).val) :=
  baseUnitsGaloisFixedEquiv (K := Kv v) (L := Lv v)
    (p := (completionRationalPrime (QPlace v)).val)

-- actual O_v units to fixed integral units
noncomputable def actualOUnitsEquiv :
    (CompletionIntegers (QPlace v))ˣ ≃* localGaloisFixedIntegralUnits
      (K := Kv v) (L := Lv v) (p := (completionRationalPrime (QPlace v)).val) :=
  (normalizedCompletionUnitsEquiv (QPlace v)).symm.trans (fixedIntegralUnits v)

-- p-adic integer units model
noncomputable def actualOUnitsPadicEquiv :
    (CompletionIntegers (QPlace v))ˣ ≃* ℤ_[⟨v.1, v.2.2.2⟩]ˣ :=
  (Units.mapEquiv (RingEquiv.cast (rationalFinitePlace_underlyingPrime v.1)).toMulEquiv).trans
    (((PadicInt.adicCompletionIntegersEquiv (R := NumberField.RingOfIntegers ℚ)
      ⟨v.1, v.2.2.2⟩).symm).toMulEquiv)

end S2035Probe4
