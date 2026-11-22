import LeanFormal.IUT.IUTII.Kummer.MonoAnalyticLogShellArchPsiCnsCalibration
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActionCompatibility

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: MonoAnalyticLogShellArchPsiCnsCalibration|SourceLogShellXMuChainActionCompatibility|SourceLogShellTensorLegCompletion -> hits IUTII/Kummer/MonoAnalyticLogShellArchPsiCnsCalibration.lean:45/206, SourceLogShellActionCompatibility.lean:87/105/127/145/163/170/178/204/221/233, SourceLogShellTensorLegCompletion:35 -> REUSE (anchor rows only; no re-proof).

# [AbsTopIII] 13: Prop 5.8(v) Psi_cns / direct factors / ±1 actions - tree anchors

Corpus: papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt
Prop 5.8 (v) (region ~8100-8200): Psi_cns calibration, direct factors, ±1
actions.  Tree anchors (all concrete p-adic/formalizable, C):
- MonoAnalyticLogShellArchPsiCnsCalibration (IUTII/Kummer; the Psi_cns shadow);
- SourceLogShellActionCompatibility:87 structure SourceLogShellXMuChainActionCompatibility
  with equivariance :105, orbit :113, logShell preservation :127/:145, IQSpan maps
  :163/:170/:178, packet equivariance :187; log-volume compatibility :204/:221/:233;
- SourceLogShellTensorLegCompletion:35 (tensor leg completion).
Anchor rows only; no new proof; no closure claims.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.AbsTopIII13PsiCnsAnchorActual


/-- A Prop 5.8(v) anchor row: (item, tree anchor, status). -/
structure PsiCnsAnchorRow where
  item : String
  anchor : String
  status : String

/-- The Prop 5.8(v) Psi_cns anchor rows. -/
def psiCnsAnchorRows : List PsiCnsAnchorRow :=
  [ { item := "Psi_cns calibration (mono-analytic arch)",
      anchor := "MonoAnalyticLogShellArchPsiCnsCalibration:45 namespace (whole file)",
      status := "C tree shadow (reuse)" }
  , { item := "direct factors / ±1 actions (x-mu chain)",
      anchor := "SourceLogShellActionCompatibility:87 structure; :105 equivariance; :113 orbit; :127/:145 logShell preservation; :163/:170/:178 IQSpan maps; :187 packet equivariance",
      status := "C elementary action facts (reuse)" }
  , { item := "log-volume compatibility of the action chain",
      anchor := "SourceLogShellActionCompatibility:204/:221/:233",
      status := "C log-volume compatibility shadow (reuse)" }
  , { item := "tensor leg completion",
      anchor := "SourceLogShellTensorLegCompletion:35",
      status := "C tensor leg (reuse)" } ]

/-- The Psi_cns anchor record has four rows. -/
theorem psiCnsAnchorRows_length : psiCnsAnchorRows.length = 4 := rfl

#check PsiCnsAnchorRow
#check psiCnsAnchorRows
#check psiCnsAnchorRows_length

end LeanFormal.IUT.XiFPaper.AbsTopIII13PsiCnsAnchorActual