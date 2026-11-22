import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceGaloisLogShell
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import Mathlib.FieldTheory.KrullTopology

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

namespace S2035Probe3

variable (v : FinitePrimePlace 2 7)
local instance : Fact (Nat.Prime v.1) := ⟨v.2.2.2⟩

-- variant A: rationalFinitePlace directly
example : Completion (rationalFinitePlace v.1) = (rationalHeightOneSpectrum v.1).adicCompletion ℚ := rfl

-- variant B: finitePrimePlaceToQ
example : Completion (LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual.finitePrimePlaceToQ v) =
    Completion (rationalFinitePlace v.1) := rfl

-- algebra instance with rationalFinitePlace
example : Algebra (NormalizedCompletion (rationalFinitePlace v.1))
    (SourceAlgebraicClosure (rationalFinitePlace v.1)) := inferInstance

-- p-adic field equiv with rationalFinitePlace
noncomputable def completionPadicEquiv :
    ℚ_[v.1] ≃+* NormalizedCompletion (rationalFinitePlace v.1) :=
  (rationalFinitePlacePadicEquiv v.1).toRingEquiv

-- p-adic integer equiv, check type
#check PadicInt.adicCompletionIntegersEquiv (R := NumberField.RingOfIntegers ℚ) ⟨v.1, v.2.2.2⟩
example : Nonempty (ℤ_[⟨v.1, v.2.2.2⟩] ≃+* CompletionIntegers (rationalFinitePlace v.1)) :=
  ⟨(PadicInt.adicCompletionIntegersEquiv (R := NumberField.RingOfIntegers ℚ) ⟨v.1, v.2.2.2⟩).symm⟩

-- algebraic closure equiv with rationalFinitePlace
noncomputable def eAlgClosure :
    AlgebraicClosure ℚ_[v.1] ≃+* SourceAlgebraicClosure (rationalFinitePlace v.1) :=
  IsAlgClosure.equivOfEquiv (L := AlgebraicClosure ℚ_[v.1])
    (M := SourceAlgebraicClosure (rationalFinitePlace v.1))
    (S := ℚ_[v.1]) (R := NormalizedCompletion (rationalFinitePlace v.1))
    (completionPadicEquiv v)

end S2035Probe3
