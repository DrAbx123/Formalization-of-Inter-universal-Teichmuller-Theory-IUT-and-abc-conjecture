import tmp.sheaf.xif.paper.S2045OperationKummerActual

-- S2046: component reduction of S2045OperationKummerData.
-- Actual constituents are the S2045 local carrier/action and psiEvaluation;
-- the three operation-comparison components remain exact missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2046OperationComponentsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1973PsiCnsActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2045OperationKummerActual

variable (v : FinitePrimePlace 2 7) (l : PrimeGeFive)

local instance (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) := ⟨v.prime⟩

/-- Actual local O^x carrier. -/
abbrev S2046LocalUnits : Type := S2045LocalUnits (v := v)

noncomputable abbrev S2046LocalAction :
    LocalAbsoluteGalois v.1 →* MulAut (S2046LocalUnits (v := v)) :=
  S2045LocalAction v

abbrev S2046LocalUnitsMu : Type := S2045LocalUnitsMu (v := v)

noncomputable abbrev S2046LocalMuAction :
    LocalAbsoluteGalois v.1 →* MulAut (S2046LocalUnitsMu (v := v)) :=
  S2045LocalMuAction v

theorem S2046LocalUnitsMu_nontrivial :
    (TimesMuQuotient.quotientMap (@localOFieldUnit v.1 ⟨v.prime⟩) :
      S2046LocalUnitsMu (v := v)) ≠ 1 :=
  S2045LocalUnitsMu_nontrivial v

noncomputable def S2046PsiEvaluationEquiv :
    PsiEnvModel v ≃* PsiGauModel v l :=
  S2045PsiEvaluationEquiv v l

/-- (a) exact missing: Galois comparison LocalAbsoluteGalois v.1 with Gv v. -/
abbrev S2046GaloisEquivRequired : Type := S2045GaloisEquiv (v := v)

/-- (b) exact missing: action-compatible actual local O^x with Psi_cns^x. -/
abbrev S2046LocalToPsiRequired : Type := S2045LocalToPsiEquiv (v := v)

def S2046LocalToPsiActionCompatible
    (g : S2046GaloisEquivRequired (v := v))
    (e : S2046LocalToPsiRequired (v := v)) : Prop :=
  S2045LocalToPsiActionCompatible (v := v) g e

/-- (c) exact missing: evaluation-compatible actual local O^x with Gau units. -/
abbrev S2046LocalToGauRequired : Type :=
  S2045LocalToGauUnitsEquiv v l

def S2046EvaluationCompatible
    (ePsi : S2046LocalToPsiRequired (v := v))
    (eGau : S2046LocalToGauRequired (v := v) (l := l)) : Prop :=
  ∀ u : S2046LocalUnits (v := v),
    (S2046PsiEvaluationEquiv v l)
      (psiEnvUnitSection v (ePsi u)) =
    (eGau u : PsiGauModel v l)

/-- Conditional assembly: the three missing components construct
S2045OperationKummerData. -/
noncomputable def S2046OperationKummerDataOfComponents
    (g : S2046GaloisEquivRequired (v := v))
    (ePsi : S2046LocalToPsiRequired (v := v))
    (hPsi : S2046LocalToPsiActionCompatible (v := v) g ePsi)
    (eGau : S2046LocalToGauRequired (v := v) (l := l))
    (hEval : S2046EvaluationCompatible (v := v) (l := l) ePsi eGau) :
    S2045OperationKummerData v l :=
  { galoisEquiv := g
    localToPsi := ePsi
    localToPsi_action := hPsi
    localToGau := eGau
    evaluation_compat := hEval }

/-- The component reduction is exactly the S2045 operation data. -/
def S2046OperationComponentsRequired : Type :=
  S2045OperationKummerRequired v l

#check S2046LocalUnits
#check S2046LocalAction
#check S2046LocalUnitsMu_nontrivial
#check S2046PsiEvaluationEquiv
#check S2046GaloisEquivRequired
#check S2046LocalToPsiRequired
#check S2046LocalToPsiActionCompatible
#check S2046LocalToGauRequired
#check S2046EvaluationCompatible
#check S2046OperationKummerDataOfComponents
#check S2046OperationComponentsRequired

#print axioms S2046LocalUnitsMu_nontrivial
#print axioms S2046PsiEvaluationEquiv
#print axioms S2046OperationKummerDataOfComponents

end LeanFormal.IUT.XiFPaper.S2046OperationComponentsActual

end