import tmp.sheaf.xif.paper.S2039ActualPsiCns
import tmp.sheaf.xif.paper.S2045OperationKummerActual

-- S2046 components (b)/(c) against S2039 actual PsiCns.
-- Actual PsiCns carrier is S2039's inverse image of zhatNonneg; the local
-- O^x-to-PsiCns and local-to-Gau comparisons remain exact missing (M1/M4).

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2046PsiCnsActualComponents

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2039ActualPsiCns
open LeanFormal.IUT.XiFPaper.S1973PsiCnsActual
open LeanFormal.IUT.XiFPaper.S2045OperationKummerActual

variable (v : FinitePrimePlace 2 7) (l : PrimeGeFive)
local instance (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) := ⟨v.prime⟩

/-- S2039 actual Psi_cns at v.1, for a normalization N. -/
abbrev S2046PsiCns (N : PsiCnsNormalization v.1) : Submonoid (PsiCnsCohomology v.1) :=
  PsiCns v.1 N

/-- The unit group of the actual Psi_cns. -/
abbrev S2046PsiCnsUnits (N : PsiCnsNormalization v.1) : Type :=
  (S2046PsiCns (v := v) N)ˣ

/-- Exact first missing M4: the normalization surjection of S2039/S2011. -/
abbrev S2046PsiCnsNormalizationRequired : Type := PsiCnsNormalization v.1

/-- Exact first missing (b): an action-compatible identification of the
actual local O^x with the unit group of the actual Psi_cns. -/
abbrev S2046LocalToPsiCnsRequired (N : PsiCnsNormalization v.1) : Type :=
  S2045LocalUnits (v := v) ≃* S2046PsiCnsUnits (v := v) N

/-- The actual G_v-action on the Psi_cns unit group is also missing; this
records its exact type, no inhabitant. -/
structure S2046PsiCnsUnitActionData (N : PsiCnsNormalization v.1) where
  action : LocalAbsoluteGalois v.1 →* MulAut (S2046PsiCnsUnits (v := v) N)

def S2046LocalToPsiCnsActionCompatible (N : PsiCnsNormalization v.1)
    (A : S2046PsiCnsUnitActionData (v := v) N)
    (e : S2046LocalToPsiCnsRequired (v := v) N) : Prop :=
  ∀ (g : LocalAbsoluteGalois v.1) (u : S2045LocalUnits (v := v)),
    e (S2045LocalAction v g u) = A.action g (e u)

/-- Exact (c) surface: evaluation-compatible local-to-Gau comparison. -/
abbrev S2046LocalToGauRequired : Type :=
  S2045LocalToGauUnitsEquiv (v := v) (l := l)

/-- Exact evaluation comparison on the actual Psi_cns side: a monoid map
from the Psi_cns unit group to the evaluated Gaussian monoid.  No inhabitant is
asserted. -/
abbrev S2046PsiToGauRequired (N : PsiCnsNormalization v.1) : Type :=
  S2046PsiCnsUnits (v := v) N →* (PsiGauModel v l)ˣ

def S2046EvaluationCompatible
    (N : PsiCnsNormalization v.1)
    (ePsi : S2046LocalToPsiCnsRequired (v := v) N)
    (eGau : S2046LocalToGauRequired (v := v) (l := l))
    (eEval : S2046PsiToGauRequired (v := v) (l := l) N) : Prop :=
  ∀ u : S2045LocalUnits (v := v),
    eEval (ePsi u) = eGau u

/-- The first-milestone actual-PsiCns operation comparison data. -/
structure S2046ActualPsiCnsOperationData where
  normalization : PsiCnsNormalization v.1
  localToPsi : S2046LocalToPsiCnsRequired (v := v) normalization
  psiAction : S2046PsiCnsUnitActionData (v := v) normalization
  localToPsi_action :
    S2046LocalToPsiCnsActionCompatible (v := v) normalization psiAction localToPsi
  localToGau : S2046LocalToGauRequired (v := v) (l := l)
  evaluation : S2046PsiToGauRequired (v := v) (l := l) normalization
  evaluation_compat :
    S2046EvaluationCompatible (v := v) (l := l) normalization
      localToPsi localToGau evaluation

abbrev S2046ActualPsiCnsOperationRequired : Type :=
  S2046ActualPsiCnsOperationData v l

#check S2046PsiCns
#check S2046PsiCnsUnits
#check S2046PsiCnsNormalizationRequired
#check S2046LocalToPsiCnsRequired
#check S2046PsiCnsUnitActionData
#check S2046LocalToPsiCnsActionCompatible
#check S2046LocalToGauRequired
#check S2046EvaluationCompatible
#check S2046ActualPsiCnsOperationData
#check S2046ActualPsiCnsOperationRequired

end LeanFormal.IUT.XiFPaper.S2046PsiCnsActualComponents

end