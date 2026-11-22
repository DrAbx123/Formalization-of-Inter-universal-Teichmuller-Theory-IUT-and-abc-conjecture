/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QPilotLineBundleFromSource
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic

/-!
# P7/#3 Route B: actual q-pilot determinant line + relative determinant map

Status: PARTIAL ACTUAL CONSTRUCTION + PRECISE MISSING.  Given the actual q-pilot
line-bundle source, construct the actual rank-one determinant line, the relative
determinant map, and the actual determinant log-volume data.  The equality with
the S3137 normalized Theta reading is recorded as a missing Proposition, not
assumed as a completed input.  No sorry/axiom.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual

universe ua uv upi umon ui

variable {l : PrimeGeFive}

/-- Actual rank-one q-pilot determinant line. -/
noncomputable def qPilotDetLine
    (A : InitialThetaArithmeticData l)
    (S : LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperQPilotLineBundleSource A) :
    LeanFormal.IUT.XiFPaperArithmeticLineBundle.SourceLineBundle (A := A) :=
  LeanFormal.IUT.PaperOModuleActual.determinantLine (k := A.K) S.qPilotLineBundle

theorem qPilotDetLine_eq
    (A : InitialThetaArithmeticData l)
    (S : LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperQPilotLineBundleSource A) :
    qPilotDetLine A S = S.qPilotLineBundle := rfl

/-- Relative determinant map for the rank-one q-pilot line bundle. -/
noncomputable def qPilotDetMap
    (A : InitialThetaArithmeticData l)
    (S : LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperQPilotLineBundleSource A) :
    qPilotDetLine A S ≃ S.qPilotLineBundle := Equiv.refl _

/-- Actual determinant/log-volume data of the q-pilot determinant line. -/
noncomputable def qPilotDetData
    (A : InitialThetaArithmeticData l)
    (S : LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperQPilotLineBundleSource A) :
    LeanFormal.IUT.PaperDeterminantLogVolume.PaperDeterminantLogVolumeData (k := A.K) :=
  LeanFormal.IUT.PaperDeterminantLogVolume.actualDeterminantLogVolumeData
    (k := A.K) S.qPilotLineBundle

/-- Actual arithmetic degree of the q-pilot determinant line. -/
noncomputable def qPilotDetArithmeticDegree
    (A : InitialThetaArithmeticData l)
    (S : LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperQPilotLineBundleSource A) : Real :=
  (qPilotDetData A S).globalLogVolume

theorem qPilotDetData_determinantLine_eq
    (A : InitialThetaArithmeticData l)
    (S : LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperQPilotLineBundleSource A) :
    (qPilotDetData A S).determinantLine = S.qPilotLineBundle := rfl

theorem qPilotDetArithmeticDegree_eq_globalLogVolume
    (A : InitialThetaArithmeticData l)
    (S : LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperQPilotLineBundleSource A) :
    qPilotDetArithmeticDegree A S =
      LeanFormal.IUT.PaperDeterminantLogVolume.globalLogVolume (k := A.K) S.qPilotLineBundle :=
  rfl

/-- Actual normalized S3137 Theta reading on C3. -/
noncomputable def routeBThetaNormalized
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Real :=
  thetaPilotHullLogVolumeReal C3 / (c3TensorBlockDimension C3 : Real)

/-- Exact missing Proposition (Route B). -/
def RouteBArithmeticDegreeReadingGap
    (A : InitialThetaArithmeticData l)
    (S : LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperQPilotLineBundleSource A)
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  qPilotDetArithmeticDegree A S = routeBThetaNormalized C3

theorem routeB_gap_iff
    (A : InitialThetaArithmeticData l)
    (S : LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperQPilotLineBundleSource A)
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    RouteBArithmeticDegreeReadingGap A S C3 ↔
      qPilotDetArithmeticDegree A S = routeBThetaNormalized C3 := Iff.rfl

def routeBB5Rows : List (String × String × String) :=
  [ ("qPilotDetLine", "rank-one determinant line = q-pilot line bundle", "CONSTRUCTED (rfl)"),
    ("qPilotDetMap", "relative determinant map", "CONSTRUCTED (Equiv.refl)"),
    ("qPilotDetArithmeticDegree", "actual determinant global log-volume", "CONSTRUCTED"),
    ("RouteBArithmeticDegreeReadingGap", "arithmetic degree = S3137 normalized reading", "MISSING exact Proposition") ]

theorem routeBB5Rows_length : routeBB5Rows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineActual
