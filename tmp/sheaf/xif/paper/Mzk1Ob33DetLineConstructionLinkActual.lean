/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineActual
import tmp.sheaf.xif.paper.Mzk1DetLineConstructionActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import Mathlib.Tactic

/-!
# P7/#3 Route B4.4: q-pilot determinant degree via the mainline relative determinant

Status: CONDITIONAL on the actual q-pilot line identification.  The mainline
relative determinant line and its global log-volume difference are reused; the
only missing equality is the actual q-pilot source line identification.
No sorry/axiom.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineConstructionLinkActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaperArithmeticLineBundle

universe ua uv upi umon ui

variable {l : PrimeGeFive}
variable (A : InitialThetaArithmeticData l)

/-- For a line bundle that is identified with the mainline relative determinant,
the q-pilot determinant arithmetic degree is the relative log-volume. -/
theorem qPilotDetArithmeticDegree_eq_relativeDetLog
    (S : PaperQPilotLineBundleSource A)
    (H O : PaperDeterminantLogVolume.LineBundle (k := A.K)) (hH : H ≠ 0) (hO : O ≠ 0)
    (hline : S.qPilotLineBundle = relativeDetLine (k := A.K) H O) :
    qPilotDetArithmeticDegree A S =
      PaperDeterminantLogVolume.globalLogVolume (k := A.K) H - PaperDeterminantLogVolume.globalLogVolume (k := A.K) O := by
  rw [qPilotDetArithmeticDegree_eq_globalLogVolume A S, hline,
    globalLogVolume_relativeDetLine (k := A.K) H O hH hO]

/-- The relative determinant line localized at a finite place. -/
noncomputable def relativeDetLocalizedLine
    (H O : PaperDeterminantLogVolume.LineBundle (k := A.K)) (v : NumberField.FinitePlace A.K) :
    Submodule (PaperOModuleActual.LocalRing (k := A.K) v)
      (PaperOModuleActual.LocalField (k := A.K) v) :=
  PaperOModuleActual.localizedLine (k := A.K) (relativeDetLine (k := A.K) H O) v

theorem relativeDetLocalizedLine_eq
    (H O : PaperDeterminantLogVolume.LineBundle (k := A.K)) (v : NumberField.FinitePlace A.K) :
    relativeDetLocalizedLine (A := A) H O v =
      PaperOModuleActual.localizedLine (k := A.K)
        (relativeDetLine (k := A.K) H O) v := rfl

/-- Fill the mainline per-place generator datum from an actual generator with a
proved span identity (no existence assertion). -/
noncomputable def localGeneratorDataOfSpan
    (I : PaperDeterminantLogVolume.LineBundle (k := A.K))
    (v : NumberField.FinitePlace A.K)
    (x : PaperOModuleActual.LocalField (k := A.K) v)
    (hspan : PaperOModuleActual.localizedLine (k := A.K) I v =
      Submodule.span (PaperOModuleActual.LocalRing (k := A.K) v) {x}) :
    LocalGeneratorData (k := A.K) I v where
  generator := x
  span_eq := hspan

theorem localGeneratorDataOfSpan_generator
    (I : PaperDeterminantLogVolume.LineBundle (k := A.K))
    (v : NumberField.FinitePlace A.K)
    (x : PaperOModuleActual.LocalField (k := A.K) v)
    (hspan : PaperOModuleActual.localizedLine (k := A.K) I v =
      Submodule.span (PaperOModuleActual.LocalRing (k := A.K) v) {x}) :
    (localGeneratorDataOfSpan (A := A) I v x hspan).generator = x := rfl

def b5Rows : List (String × String × String) :=
  [ ("qPilotDetArithmeticDegree_eq_relativeDetLog", "mainline relativeDetLine gives global log-volume difference", "PROVED conditional on actual q-pilot line identification"),
    ("relativeDetLocalizedLine", "actual finite-place localization of relative determinant", "CONSTRUCTED"),
    ("B5 per-place index/SNF", "finite-index/Smith normal form object on localizedLine", "MISSING exact object"),
    ("archimedean metric", "infinite-place determinant metric", "MISSING exact object") ]

theorem b5Rows_length : b5Rows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineConstructionLinkActual
