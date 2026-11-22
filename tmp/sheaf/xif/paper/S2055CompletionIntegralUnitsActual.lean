import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
namespace LeanFormal.IUT.XiFPaper.S2055CompletionIntegralUnitsActual
variable (place : NumberField.FinitePlace ℚ)
/-- The actual completion QPlace integral units: units of the valuation ring
of the spectral-norm algebraic closure. -/
abbrev S2055CompletionIntegralUnits : Type :=
  (Integers (SourceAlgebraicClosure place))ˣ
/-- The Q_p-model integral units of S1978 as a comparison target. -/
abbrev S2055QpIntegralUnits (place : NumberField.FinitePlace ℚ) : Type :=
  (Integers (AlgebraicClosure ℚ_[completionRationalPrime place]))ˣ
theorem S2055CompletionIntegralUnits_nonempty :
    Nonempty (S2055CompletionIntegralUnits place) :=
  ⟨1⟩
/-- Actual O^×μ quotient at the completion carrier (no identification with the
Q_p model is asserted). -/
abbrev S2055CompletionOUnitsMu (place : NumberField.FinitePlace ℚ) : Type :=
  TimesMuQuotient (S2055CompletionIntegralUnits place)
theorem S2055CompletionOUnitsMu_nonempty :
    Nonempty (S2055CompletionOUnitsMu place) :=
  ⟨TimesMuQuotient.quotientMap 1⟩
/-- The exact missing completion-to-Q_p integral-units identification: a
norm-preserving/valuation-ring-preserving group isomorphism.  No inhabitant is
asserted; algClosureEquiv alone is only a ring equivalence. -/
abbrev S2055IntegralUnitsIdentificationRequired
    (place : NumberField.FinitePlace ℚ) : Type :=
  S2055CompletionIntegralUnits place ≃* S2055QpIntegralUnits place
/-- Exact missing rebased paper input (S1978). -/
abbrev S2055RebasedPaperInputRequired
    (D : S1895OIdentificationsActual.S1895PaperInput) : Type 1 :=
  S1978RebasedPaperInput D
#check S2055CompletionIntegralUnits
#check S2055CompletionIntegralUnits_nonempty
#check S2055CompletionOUnitsMu
#check S2055CompletionOUnitsMu_nonempty
#check S2055IntegralUnitsIdentificationRequired
#check S2055RebasedPaperInputRequired
end LeanFormal.IUT.XiFPaper.S2055CompletionIntegralUnitsActual
end
