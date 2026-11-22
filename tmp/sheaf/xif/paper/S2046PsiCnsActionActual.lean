import tmp.sheaf.xif.paper.S2039ActualPsiCns
import tmp.sheaf.xif.paper.S2045OperationKummerActual
import tmp.sheaf.xif.paper.S2046PsiCnsActualComponents

-- S2046 (b): conditional actual PsiCns-units <-> O^tri_{F_v} units
-- equivalence from the S2039 normalization/exhaustion theorem, and the
-- exact missing local O^x-to-O^tri bridge.  No fake.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2046PsiCnsActionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2039ActualPsiCns
open LeanFormal.IUT.XiFPaper.S2045OperationKummerActual
open LeanFormal.IUT.XiFPaper.S2046PsiCnsActualComponents

variable (v : FinitePrimePlace 2 7) (l : PrimeGeFive)
local instance (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) := ⟨v.prime⟩

/-- Conditional actual: under the S2039 normalization/valuation and
    exhaustion assertions, the unit group of actual Psi_cns is the unit group
    of O^tri_{F_v}. -/
noncomputable def S2046PsiCnsUnitsEquivOtriFv
    (N : PsiCnsNormalization v.1)
    (hval : NormalizationIsValuation v.1 N)
    (hex : PsiCnsExhaustion v.1 N) :
    S2046PsiCnsUnits (v := v) N ≃* (OtriFv v.1)ˣ :=
  Units.mapEquiv
    (Classical.choice (PsiCns_equiv_otriFv v.1 N hval hex))

/-- Exact missing local-model bridge: actual local O^x (S1978 algebraic-
    closure integral units) to the units of O^tri_{F_v}. -/
abbrev S2046LocalToOtriFvRequired : Type :=
  S2045LocalUnits (v := v) ≃* (OtriFv v.1)ˣ

/-- Conditional actual reduction: the local bridge plus S2039's
    normalization/exhaustion gives the local O^x-to-Psi_cns group
    equivalence. -/
noncomputable def S2046LocalToPsiCnsOfBridge
    (N : PsiCnsNormalization v.1)
    (hval : NormalizationIsValuation v.1 N)
    (hex : PsiCnsExhaustion v.1 N)
    (e : S2046LocalToOtriFvRequired (v := v)) :
    S2046LocalToPsiCnsRequired (v := v) N :=
  e.trans (S2046PsiCnsUnitsEquivOtriFv (v := v) N hval hex).symm

/-- M4 exact first missing: existence of the S2039 normalization. -/
abbrev S2046M4NormalizationRequired : Prop :=
  NormalizationMissing v.1

/-- M4 reduction: the S2039 pair (valuation, exhaustion) supplies the
    normalization and hence the Psi_cns-units/O^tri-units equivalence. -/
theorem S2046M4_sufficient
    (N : PsiCnsNormalization v.1)
    (hval : NormalizationIsValuation v.1 N)
    (hex : PsiCnsExhaustion v.1 N) :
    Nonempty (S2046PsiCnsUnits (v := v) N ≃* (OtriFv v.1)ˣ) :=
  ⟨S2046PsiCnsUnitsEquivOtriFv (v := v) N hval hex⟩

/-- M4 reduction to the source H^2/normalization: if the S2039
    `Cor110bKummerIdentification` holds, the normalization and the
    identification exist. -/
theorem S2046M4_of_cor110b
    (h : Cor110bKummerIdentification v.1) :
    Nonempty (S2046PsiCnsUnits (v := v) h.choose ≃* (OtriFv v.1)ˣ) :=
  S2046M4_sufficient (v := v) h.choose h.choose_spec.1 h.choose_spec.2

#check S2046PsiCnsUnitsEquivOtriFv
#check S2046LocalToOtriFvRequired
#check S2046LocalToPsiCnsOfBridge
#check S2046M4NormalizationRequired
#check S2046M4_sufficient
#check S2046M4_of_cor110b

#print axioms S2046PsiCnsUnitsEquivOtriFv
#print axioms S2046LocalToPsiCnsOfBridge
#print axioms S2046M4_sufficient
#print axioms S2046M4_of_cor110b

end LeanFormal.IUT.XiFPaper.S2046PsiCnsActionActual

end