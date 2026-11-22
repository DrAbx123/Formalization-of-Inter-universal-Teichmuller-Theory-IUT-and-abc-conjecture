/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1S3137LChainActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import Mathlib.Tactic

/-! # A994: signed real log-volume for the L model

`SourceImageHullVolume` uses `ENNReal.ofReal (sourceLocalLogDegree ...)`, which
truncates negative log-degrees; under the realified producer the hull volume is
then `⊤` and `toReal` gives 0.  This file replaces the ENNReal (nonnegative)
volume by a **signed real log-volume** `sSup (sourceLocalLogDegree '' S)`, keeping
negative values, and defines the signed theta-hull log-volume and its global sum.

`SignedVolumeAgreesWithSetVolume` and `PaperRIdentification` are explicit Props,
not proved: the identification with the paper/`RHSData.vol` log-volume is a GAP.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1RealifiedValueMonoidActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137LChainActual

variable {l : PrimeGeFive} {V : Type*} [Fintype V] (I : OriginalInput l V)

/-- Signed real log-volume of a set of value points: supremum of local log-degrees. -/
noncomputable def sourceLogVolumeSigned (v : V) (S : Set (I.ThetaPilotPoint v)) : ℝ :=
  sSup (I.sourceLocalLogDegree v '' S)

theorem sourceLogVolumeSigned_eq (v : V) (S : Set (I.ThetaPilotPoint v)) :
    sourceLogVolumeSigned (I := I) v S = sSup (I.sourceLocalLogDegree v '' S) := rfl

/-- A value point's log-degree is at most the signed volume, when the image is
nonempty and bounded above. -/
theorem sourceLocalLogDegree_le_sourceLogVolumeSigned (v : V)
    (S : Set (I.ThetaPilotPoint v)) (hS : S.Nonempty)
    (hb : BddAbove (I.sourceLocalLogDegree v '' S)) {x : I.ThetaPilotPoint v}
    (hx : x ∈ S) :
    I.sourceLocalLogDegree v x ≤ sourceLogVolumeSigned (I := I) v S := by
  unfold sourceLogVolumeSigned
  exact le_csSup hb ⟨x, hx, rfl⟩

/-- If the image is nonempty and bounded above, the signed volume is an upper bound. -/
theorem sourceLogVolumeSigned_upper (v : V) (S : Set (I.ThetaPilotPoint v))
    (hb : BddAbove (I.sourceLocalLogDegree v '' S)) :
    ∀ y ∈ I.sourceLocalLogDegree v '' S, y ≤ sourceLogVolumeSigned (I := I) v S := by
  intro y hy
  unfold sourceLogVolumeSigned
  exact le_csSup hb hy

/-- Finiteness/compactness-style hypothesis for the signed volume. -/
def SignedVolumeFinite (v : V) (S : Set (I.ThetaPilotPoint v)) : Prop :=
  S.Nonempty ∧ BddAbove (I.sourceLocalLogDegree v '' S)

/-- Agreement of the ENNReal set-volume logarithm with the signed volume (GAP). -/
def SignedVolumeAgreesWithSetVolume (v : V) (S : Set (I.ThetaPilotPoint v)) : Prop :=
  Real.log (I.sourceSetVolume v S).toReal = sourceLogVolumeSigned (I := I) v S

/-- Theta-hull signed log-volume at a place. -/
noncomputable def thetaHullLogVolumeAtSigned (v : V)
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) : ℝ :=
  sourceLogVolumeSigned (I := I) v (I.sourceHolomorphicHull v (R v) n)

/-- Global signed theta-hull log-volume: sum over places. -/
noncomputable def globalThetaHullLogVolumeSigned
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) : ℝ :=
  ∑ v : V, thetaHullLogVolumeAtSigned I v R n

theorem globalThetaHullLogVolumeSigned_eq
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    globalThetaHullLogVolumeSigned I R n =
      ∑ v : V, thetaHullLogVolumeAtSigned (I := I) v R n := rfl

/-- Explicit identification with the paper RHS: `R = -rhs` (GAP field). -/
def PaperRIdentification (R lhs : ℝ) : Prop := R = -lhs

def PaperRIdentification_iff (R lhs : ℝ) :
    PaperRIdentification R lhs ↔ R = -lhs := Iff.rfl

variable [Fintype S1487W]

/-- Signed L chain at the concrete S1487 input: per-place signed theta-hull volume. -/
noncomputable def thetaHullLogVolumeAtSignedL
    (hreal : S1487RealificationHypothesis (l := l))
    (n : ThetaPilotCarrier l) (v : S1487W) : ℝ :=
  sourceLogVolumeSigned (I := S1487Input (l := l)) v
    ((S1487Input (l := l)).sourceHolomorphicHull v
      (S1487R (l := l) hreal v) n)

/-- Signed L chain: global signed theta-hull log-volume. -/
noncomputable def globalThetaHullLogVolumeSignedL
    (hreal : S1487RealificationHypothesis (l := l))
    (n : ThetaPilotCarrier l) : ℝ :=
  ∑ v : S1487W, thetaHullLogVolumeAtSignedL (l := l) hreal n v

theorem globalThetaHullLogVolumeSignedL_eq
    (hreal : S1487RealificationHypothesis (l := l))
    (n : ThetaPilotCarrier l) :
    globalThetaHullLogVolumeSignedL (l := l) hreal n =
      ∑ v : S1487W, thetaHullLogVolumeAtSignedL (l := l) hreal n v := rfl

def rows : List (String × String × String) :=
  [ ("sourceLogVolumeSigned", "sSup of sourceLocalLogDegree image (signed)", "DEF"),
    ("le/upper", "sSup properties under Nonempty/BddAbove", "PROVED"),
    ("SignedVolumeFinite", "Nonempty + BddAbove", "DEF (compactness/finiteness pattern)"),
    ("SignedVolumeAgreesWithSetVolume", "log(toReal(sourceSetVolume)) = signed", "GAP (not proved)"),
    ("thetaHullLogVolumeAtSigned", "per-place signed hull volume", "DEF"),
    ("globalThetaHullLogVolumeSigned", "sum over places", "DEF + rfl"),
    ("thetaHullLogVolumeAtSignedL/global...SignedL", "A989 replacement at S1487", "DEF + rfl"),
    ("PaperRIdentification", "R = -rhs link to RHSData.vol", "GAP field"),
    ("sourceSetVolume signed agreement", "ENNReal truncation issue", "GAP (A993)") ]

theorem rows_length : rows.length = 9 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeActual.sourceLocalLogDegree_le_sourceLogVolumeSigned
#print axioms LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeActual.globalThetaHullLogVolumeSignedL_eq

end LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeActual

end