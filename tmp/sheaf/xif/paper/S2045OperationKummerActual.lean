import tmp.sheaf.xif.paper.S1973PsiCnsActual
import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
import tmp.sheaf.xif.paper.S1951KummerEvaluationSquareActual

-- S2045: operation-level Kummer/evaluation first milestone on the actual
-- local O^x / O^xmu carrier.  No S1487 trivial carrier or Q_p model is used.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2045OperationKummerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1973PsiCnsActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual

variable (v : FinitePrimePlace 2 7) (l : PrimeGeFive)

local instance (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) := ⟨v.prime⟩

/-- Actual local O^x carrier (units of the valuation integers in the
    algebraic closure of Q_p). -/
abbrev S2045LocalUnits : Type := LocalOFieldUnitsAt v

/-- Actual local O^x action of the local absolute Galois group. -/
noncomputable abbrev S2045LocalAction :
    LocalAbsoluteGalois v.1 →* MulAut (S2045LocalUnits (v := v)) :=
  LocalOFieldUnitsActionAt v

/-- Actual local O^xmu quotient. -/
abbrev S2045LocalUnitsMu : Type := LocalOFieldUnitsMuAt v

noncomputable abbrev S2045LocalMuAction :
    LocalAbsoluteGalois v.1 →* MulAut (S2045LocalUnitsMu (v := v)) :=
  LocalOFieldUnitsMuActionAt v

/-- The local O^xmu carrier is nontrivial: the actual local unit 1+p is not
    torsion. -/
theorem S2045LocalUnitsMu_nontrivial :
    (TimesMuQuotient.quotientMap (@localOFieldUnit v.1 ⟨v.prime⟩) :
      S2045LocalUnitsMu (v := v)) ≠ 1 :=
  LocalOFieldUnitsMuAt_nontrivial v

/-- Actual psiEvaluation monoid equivalence from S1973 (bijective local
    evaluation), connecting the operation layer to Psi_env/Psi_gau. -/
noncomputable def S2045PsiEvaluationEquiv :
    PsiEnvModel v ≃* PsiGauModel v l :=
  MulEquiv.ofBijective (psiEvaluation v l) (psiEvaluation_bijective v l)

/-- Exact first missing: an action-compatible identification of the actual
    local O^x group with Psi_cns(G_v)^x. -/
abbrev S2045GaloisEquiv : Type :=
  LocalAbsoluteGalois v.1 ≃* Gv v

abbrev S2045LocalToPsiEquiv : Type :=
  S2045LocalUnits (v := v) ≃* PsiCnsUnits v

def S2045LocalToPsiActionCompatible
    (g : S2045GaloisEquiv (v := v))
    (e : S2045LocalToPsiEquiv (v := v)) : Prop :=
  ∀ (σ : LocalAbsoluteGalois v.1) (u : S2045LocalUnits (v := v)),
    e (S2045LocalAction v σ u) = psiCnsUnitsAction v (g σ) (e u)

/-- Exact first missing: identification of the actual local O^x with the
    evaluated Gaussian units. -/
abbrev S2045LocalToGauUnitsEquiv : Type :=
  S2045LocalUnits (v := v) ≃* (PsiGauModel v l)ˣ

/-- The first-milestone operation comparison data: an action-compatible
    local-to-Psi identification and an evaluation-compatible local-to-Gau
   identification.  No inhabitant is asserted. -/
structure S2045OperationKummerData where
  galoisEquiv : S2045GaloisEquiv (v := v)
  localToPsi : S2045LocalToPsiEquiv (v := v)
  localToPsi_action :
    S2045LocalToPsiActionCompatible (v := v) galoisEquiv localToPsi
  localToGau : S2045LocalToGauUnitsEquiv v l
  evaluation_compat :
    ∀ u : S2045LocalUnits (v := v),
      (S2045PsiEvaluationEquiv v l)
        (psiEnvUnitSection v (localToPsi u)) =
      (localToGau u : PsiGauModel v l)

/-- The exact first missing surface, no inhabitant. -/
abbrev S2045OperationKummerRequired : Type :=
  S2045OperationKummerData v l

#check S2045LocalUnits
#check S2045LocalAction
#check S2045LocalUnitsMu
#check S2045LocalMuAction
#check S2045LocalUnitsMu_nontrivial
#check S2045PsiEvaluationEquiv
#check S2045LocalToPsiEquiv
#check S2045LocalToPsiActionCompatible
#check S2045LocalToGauUnitsEquiv
#check S2045OperationKummerData
#check S2045OperationKummerRequired

#print axioms S2045LocalUnitsMu_nontrivial
#print axioms S2045PsiEvaluationEquiv
#print axioms S2045OperationKummerData

end LeanFormal.IUT.XiFPaper.S2045OperationKummerActual

end