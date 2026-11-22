/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1NormArchCKActual
import tmp.sheaf.xif.paper.Mzk1NormArchConsumerActual
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineBridgeActual
import Mathlib.Tactic

/-! # Route B #3 step 4: archCK/heightWeight hookup for the PlaceB5 merge -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5ArchActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchConsumerActual

variable {l : PrimeGeFive}

noncomputable def archCKForK (T : SourceNativeInitialThetaData.{0} l) : Real :=
  archCK T.arithmetic.K

theorem archCKForK_pos (T : SourceNativeInitialThetaData.{0} l) : 0 < archCKForK T := by
  unfold archCKForK
  exact archCK_pos (K := T.arithmetic.K)

theorem archCKForK_eq_heightWeight (T : SourceNativeInitialThetaData.{0} l) :
    archCKForK T = heightWeight T.arithmetic.K := by
  unfold archCKForK
  exact archCK_eq_heightWeight (K := T.arithmetic.K)

theorem hArc_nonneg_for_K (T : SourceNativeInitialThetaData.{0} l) (x : T.arithmetic.K) :
    0 <= hArc T.arithmetic.K x := by
  exact hArc_nonneg_via_archCK (F := T.arithmetic.K) x

noncomputable def mergedLogDegree (T : SourceNativeInitialThetaData.{0} l)
    (finitePart archSum : Real) : Real :=
  finitePart + archCKForK T * archSum

theorem mergedLogDegree_eq (T : SourceNativeInitialThetaData.{0} l)
    (finitePart archSum : Real) :
    mergedLogDegree T finitePart archSum =
      finitePart + archCKForK T * archSum := rfl

theorem mergedLogDegree_nonneg (T : SourceNativeInitialThetaData.{0} l)
    {finitePart archSum : Real} (hfinite : 0 <= finitePart) (harch : 0 <= archSum) :
    0 <= mergedLogDegree T finitePart archSum := by
  unfold mergedLogDegree
  have hc : 0 < archCKForK T := archCKForK_pos T
  nlinarith

def placeB5ArchRows : List (String × String × String) :=
  [ ("archCKForK", "explicit archCK = 1/[K:Q] for K = T.arithmetic.K", "CONSTRUCTED (NormArchCK)"),
    ("archCKForK_eq_heightWeight", "equals heightWeight (rfl-level)", "PROVED"),
    ("hArc_nonneg_for_K", "GenEll arch layer nonneg via archCK", "PROVED (NormArchConsumer)"),
    ("mergedLogDegree", "finite B5 part + archCK * archSum", "DEF"),
    ("mergedLogDegree_nonneg", "nonneg merged degree", "PROVED (conditional on nonneg inputs)"),
    ("PlaceB5Target", "per-place finite B5 target", "see Mzk1DetLinePlaceB5Actual") ]

theorem placeB5ArchRows_length : placeB5ArchRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5ArchActual

end