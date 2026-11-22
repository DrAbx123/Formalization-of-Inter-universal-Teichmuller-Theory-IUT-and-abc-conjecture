/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TateInstanceCoherenceActual
import Mathlib.Tactic

/-! # Mzk1TateRealizationDataActual — realization data with coherent instances (A812)

Uses the instance-coherent bridge (`Mzk1TateInstanceCoherenceActual`) so that the
completion's Mathlib `NormedField` instance is the one used on both sides.

Consequences:
* `candidate_tateCurve_eq` : the candidate's vendor Tate curve is the LeanFormal
  canonical Tate curve at the candidate's `q` (no instance mismatch);
* `candidate_canonical_isElliptic` : that canonical curve is elliptic;
* `tateComparisonDataOfCandidate` : `TateComparisonData` is assembled from the variable
  change and its realizing equality ONLY — the ellipticity field is automatic.

Remaining TRUE gaps (analytic):
* (ii) base-level realization `C • E_q = X.curve` (analytic Tate uniformization);
* (iii) `TatePointComparison` point uniformization (vendor model bridge).

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1TateRealizationDataActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1NormValDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1TateComparisonBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1TateInstanceCoherenceActual

universe u

variable {F : Type u} [Field F] [NumberField F]
variable (place : NumberField.FinitePlace F)
variable [IsUltrametricDist (Completion place)] [CompleteSpace (Completion place)]

theorem candidate_tateCurve_eq (parameter : FinitePlaceQCandidate place) :
    (tateParameterOfQCandidate place parameter).tateCurve =
      TateCurve.weierstrassCurve (Completion place) parameter.q :=
  tateParameterOfQCandidate_curve_eq' place parameter

theorem candidate_canonical_isElliptic (parameter : FinitePlaceQCandidate place) :
    (TateCurve.weierstrassCurve (Completion place) parameter.q).IsElliptic :=
  tateParameterOfQCandidate_canonical_isElliptic' place parameter

/-- **Realization data from a candidate**: only the variable change and its realizing
equality are needed; ellipticity is automatic via the coherent instance bridge. -/
def tateComparisonDataOfCandidate {X : PuncturedEllipticCurve F}
    (parameter : FinitePlaceQCandidate place)
    (C : WeierstrassCurve.VariableChange (Completion place))
    (hC : C • TateCurve.weierstrassCurve (Completion place) parameter.q =
      (X.baseChange (Completion place)).curve) :
    TateComparisonData X place parameter where
  canonicalIsElliptic := candidate_canonical_isElliptic place parameter
  coordinateChange := C
  realizesCurve := hC

def realizationRows : List (String × String) :=
  [ ("candidate → vendor TateParameter (unit + norm < 1)", "PROVED"),
    ("candidate vendor curve = LeanFormal canonical curve (coherent)", "PROVED"),
    ("candidate canonical curve elliptic (coherent)", "PROVED"),
    ("TateComparisonData from variable change + equality only", "PROVED"),
    ("(ii) base-level realization equality C • E_q = X.curve", "MISSING (analytic Tate uniformization)"),
    ("(iii) TatePointComparison point uniformization", "MISSING (model bridge)") ]

theorem realizationRows_length : realizationRows.length = 6 := rfl

#check candidate_tateCurve_eq
#check tateComparisonDataOfCandidate
#check realizationRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TateRealizationDataActual
end
