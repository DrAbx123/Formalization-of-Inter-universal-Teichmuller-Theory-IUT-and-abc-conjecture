/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S2708MultiPlaceQPilotActual
import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual
import tmp.sheaf.xif.paper.OrigXiFPaperQPilotObjectActual
import Mathlib.Tactic

/-! # A1072: the source-root identity (Route A scalar closing gap) -/

/-
| field | value |
|---|---|
| Status | PARTIAL (equivalence to the multi-place volume PROVED; the multi-place volume = -paperQAbsLog identification is the GAP) |
| 目标 | `SourceRootIdentity I logQ := OrigXiFPaperBadQAbsLog I.initial = paperQAbsLog l logQ` |
| 真证 | `sourceRootIdentity_iff_multi`; `paperQAbsLog_eq_logQ_div`; `sourceRootIdentity_of_multiVolume` |
| GAP | GAP-SOURCE-ROOT: no finite-place map badPlaces -> FinitePlace and no discrete q realization; `paperQPilotLogVolume_multi D = -paperQAbsLog l logQ` is not provable from the abstract source contract (see S2708 docstring) |
| 循环性 | no target assumed; the missing identification is an explicit hypothesis |

This file contains no sorry and no axiom.  The equivalence is real; the missing
finite-place identification is recorded as GAP-SOURCE-ROOT (S2708 obstruction). -/

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual

namespace LeanFormal.IUT.XiFPaper.Mzk1SourceRootIdentityActual

universe ua uv upi umon ui
universe uG uL uC

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- `paperQAbsLog = logQ/(2l)` (from S2691 definitions). -/
theorem paperQAbsLog_eq_logQ_div (logQ : Real) :
    paperQAbsLog l logQ = logQ / (2 * (l.value : Real)) := by
  unfold paperQAbsLog qNormFactor
  ring

/-- The source-root identity: the source bad-q absolute-log sum equals the paper |log q|. -/
def SourceRootIdentity (logQ : Real) : Prop :=
  OrigXiFPaperBadQAbsLog I.initial = paperQAbsLog l logQ

/-- The multi-place q-pilot volume equals the negated source bad-q sum. -/
theorem multiVolume_eq_neg_badQ (D : MultiPlaceQPilotDonor I) :
    paperQPilotLogVolume_multi D = -sourceBadQAbsLog I.initial :=
  paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog D

/-- **Equivalence (proved)**: the source-root identity is equivalent to the
multi-place q-pilot volume being `-paperQAbsLog`. -/
theorem sourceRootIdentity_iff_multi (D : MultiPlaceQPilotDonor I) (logQ : Real) :
    SourceRootIdentity (l := l) (I := I) logQ ↔
      paperQPilotLogVolume_multi D = -paperQAbsLog l logQ := by
  have hbad : OrigXiFPaperBadQAbsLog I.initial = sourceBadQAbsLog I.initial := rfl
  have hvol := multiVolume_eq_neg_badQ (I := I) D
  unfold SourceRootIdentity
  rw [hbad]
  constructor
  · intro h
    rw [hvol]
    linarith
  · intro h
    rw [hvol] at h
    linarith

/-- Conditional closing: the multi-place volume identity gives the source-root identity. -/
theorem sourceRootIdentity_of_multiVolume (D : MultiPlaceQPilotDonor I) (logQ : Real)
    (h : paperQPilotLogVolume_multi D = -paperQAbsLog l logQ) :
    SourceRootIdentity (l := l) (I := I) logQ :=
  (sourceRootIdentity_iff_multi (I := I) D logQ).mpr h

/-- The source-root identity with `A = logQ/(2l)` gives `badQAbsLog = A`. -/
theorem sourceRootIdentity_eq_abs (D : MultiPlaceQPilotDonor I) (logQ : Real)
    (h : paperQPilotLogVolume_multi D = -logQ / (2 * (l.value : Real))) :
    OrigXiFPaperBadQAbsLog I.initial = logQ / (2 * (l.value : Real)) := by
  have hSR : OrigXiFPaperBadQAbsLog I.initial = paperQAbsLog l logQ := by
    exact (sourceRootIdentity_iff_multi (I := I) D logQ).mpr (by
      calc paperQPilotLogVolume_multi D
          = -logQ / (2 * (l.value : Real)) := h
        _ = -(logQ / (2 * (l.value : Real))) := by rw [neg_div]
        _ = -paperQAbsLog l logQ := by rw [paperQAbsLog_eq_logQ_div])
  rw [hSR, paperQAbsLog_eq_logQ_div]

def sourceRootRows : List (String × String) :=
  [ ("paperQAbsLog_eq_logQ_div", "paperQAbsLog = logQ/(2l) (PROVED)") ,
    ("SourceRootIdentity", "badQAbsLog initial = paperQAbsLog l logQ") ,
    ("sourceRootIdentity_iff_multi", "identity <-> multi volume = -paperQAbsLog (PROVED)") ,
    ("GAP-SOURCE-ROOT", "finite-place/discrete q realization missing (S2708 obstruction)") ]

theorem sourceRootRows_length : sourceRootRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1SourceRootIdentityActual