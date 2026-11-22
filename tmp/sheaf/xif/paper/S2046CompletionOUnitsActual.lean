import tmp.sheaf.xif.paper.S2055CompletionIntegralUnitsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2055CompletionIntegralUnitsActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual

local instance s2046FactPrime (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) :=
  ⟨v.2.2.2⟩

abbrev QPlace (v : FinitePrimePlace 2 7) : NumberField.FinitePlace ℚ :=
  rationalFinitePlace v.1

/-- Canonical completion integral units: alias of S2055, no duplicate carrier. -/
abbrev CompletionOUnits (v : FinitePrimePlace 2 7) : Type :=
  S2055CompletionIntegralUnits (QPlace v)

/-- Canonical completion O^×mu quotient: alias of S2055. -/
abbrev CompletionOUnitsMu (v : FinitePrimePlace 2 7) : Type :=
  S2055CompletionOUnitsMu (QPlace v)

/-- Exact missing norm bridge, now stated with the canonical S2055
identification target; no duplicate carrier is introduced. -/
structure S2046NormBridge (v : FinitePrimePlace 2 7) where
  identification : S2055IntegralUnitsIdentificationRequired (QPlace v)
  muCompatible : CompletionOUnitsMu v ≃*
    TimesMuQuotient (S2055QpIntegralUnits (QPlace v))

end LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual
end