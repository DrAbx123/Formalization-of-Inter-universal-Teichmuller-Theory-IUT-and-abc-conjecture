/- Adapter: GChoice gates -> M2 wiring (exact-name re-exports only; no new proofs).

Approved by Lead 2026-11-17: this file ONLY re-exports the exact names of the
GChoice gate corpus for henry's `m2AnalyticTarget_of_branch` main file, with the
reference order:
  D : Mzk1ScaleData ; H : Lemma22Hypotheses D.S D.beta ;
  critical-values row (belyiPolynomial / gPoly) ;
  gChoice_avoids + gChoice_card_lt ;
  gChoiceData_of_avoids (with GChoiceUnramifiedShape) or
  gChoice_unramified_of_criticalInTarget (with GChoiceCriticalInTarget) ;
  then Mzk1G1PsiM2AnalyticActual.polyEvalP1_ofFinite_mem_specialSet_iff for the
  M2AnalyticTarget fields.

NAMED RESIDUAL (NOT closed): the existence proof of `GChoiceCriticalInTarget`
(canonical Belyi critical-points route) is still open; files
`Mzk1GChoiceCriticalIlnActual` / `Mzk1GChoiceDataActual` do not exist.  This adapter
does not claim any closure of those.
-/
import tmp.sheaf.xif.paper.Mzk1GChoiceAvoidCanonicalActual
import tmp.sheaf.xif.paper.Mzk1GChoiceUnramifiedCanonicalActual
import tmp.sheaf.xif.paper.Mzk1GChoiceUnramifiedActual
import tmp.sheaf.xif.paper.Mzk1G1PsiM2AnalyticActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceToM2Actual

open LeanFormal.IUT.XiFPaper.Mzk1GChoiceAvoidCanonicalActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedCanonicalActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual

/-- re-export: canonical Belyi critical values lie in {0,1}. -/
def gChoice_criticalValues_rat_adapter :=
  Mzk1GChoiceUnramifiedCanonicalActual.canonicalBelyi_criticalValues_row

/-- re-export: gPoly is unramified at infinity. -/
def gChoice_unramified_infty_adapter :=
  Mzk1GChoiceUnramifiedCanonicalActual.gPoly_unramified_infty

/-- re-export: the beta-avoiding row for gPoly (Branch values / aeval 0). -/
def gChoice_avoids_adapter :=
  Mzk1GChoiceAvoidCanonicalActual.gChoice_avoids

/-- re-export: the strict cardinality drop |g(S)| < |S|. -/
def gChoice_card_lt_adapter :=
  Mzk1GChoiceAvoidCanonicalActual.gChoice_card_lt

/-- re-export: unramified reduction from the critical-in-target hypothesis. -/
def gChoice_unramified_of_criticalInTarget_adapter :=
  Mzk1GChoiceUnramifiedCanonicalActual.gChoice_unramified_of_criticalInTarget

/-- re-export: the GChoiceData package from avoids + the unramified shape. -/
def gChoiceData_of_avoids_adapter :=
  Mzk1GChoiceAvoidCanonicalActual.gChoiceData_of_avoids

/-- re-export: the M2 special-set bridge for rational evaluations. -/
def polyEvalP1_specialSet_iff_adapter :=
  Mzk1G1PsiM2AnalyticActual.polyEvalP1_ofFinite_mem_specialSet_iff

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceToM2Actual
end