/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1S1487SourceRootIdentityActual
import tmp.sheaf.xif.paper.OrigXiFPaperQPilotObjectActual
import Mathlib.Tactic

/-! # A1074: concrete S1487 q-pilot volume target + volume_eq draft -/

/-
| field | value |
|---|---|
| Status | PARTIAL (target PROVED for the S1487 signed volume; S2717 initial identification and Haar volume_eq are GAPs) |
| 真证 | `S1487SignedLogVolume_eq_neg_badQ`; `S1487_qPilotVolumeTarget`; `signed_volume_eq_of_haar` |
| GAP | GAP-S2711-INITIAL: `(S2711I ...).initial = (S1487RootInput l).initial` not available; hence S2717QPilotLogVolume cannot be syntactically identified with S1487 volume |
| GAP | GAP-HAAR-REGION: `(haarLogVolume μ region).toReal = OrigXiFPaperBadQAbsLog` (the q-side Haar region volume) is the missing geometric input |
| GAP | GAP-THETA-SUBSET: `actualC3LogShellTensorRegion ⊆ region` (theta⊆q direction) still missing |
| 循环性 | no target assumed; the GAPs are explicit Prop/data fields |
-/

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.Mzk1SourceRootIdentityActual
open LeanFormal.IUT.XiFPaper.Mzk1S1487SourceRootIdentityActual
open LeanFormal.IUT.XiFPaper.OrigXiF.OrigXiFPaperQPilotObjectActual

namespace LeanFormal.IUT.XiFPaper.Mzk1S1487QPilotTargetActual

variable {l : PrimeGeFive}

/-- The concrete S1487 signed source q-pilot volume. -/
noncomputable def S1487SignedLogVolume (l : PrimeGeFive) : Real :=
  sourceQPilotSignedLog (S1487RootInput l).initial

/-- The concrete signed volume is the negative bad-q absolute-log sum. -/
theorem S1487SignedLogVolume_eq_neg_badQ (l : PrimeGeFive) :
    S1487SignedLogVolume l =
      -OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData (l := l)) := by
  unfold S1487SignedLogVolume
  rw [S1487RootInput_initial]
  exact sourceQPilotSignedLog_eq_neg_badQAbsLog _

/-- **Concrete q-pilot volume target** (S1487, canonical logQ):
`signed volume = -paperQAbsLog l (2l * badQAbsLog)`. -/
theorem S1487_qPilotVolumeTarget (l : PrimeGeFive) :
    S1487SignedLogVolume l = -paperQAbsLog l (S1487CanonicalLogQ l) := by
  unfold S1487SignedLogVolume S1487CanonicalLogQ
  rw [S1487RootInput_initial, sourceQPilotSignedLog_eq_neg_badQAbsLog]
  rw [paperQAbsLog_two_l_mul]

/-- Generic bridge for the volume_eq field: if the Haar log-volume of the q-side
region equals `paperQAbsLog`, the negative signed form matches. -/
theorem signed_volume_eq_of_haar (l : PrimeGeFive) (haarA logQ : Real)
    (h : haarA = paperQAbsLog l logQ) :
    -haarA = -paperQAbsLog l logQ := by
  rw [h]

/-- The concrete Haar/measure target for the `volume_eq` field (explicit Prop, no inhabitant). -/
def S1487HaarVolumeTarget (l : PrimeGeFive) (haarA : Real) : Prop :=
  haarA = OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData (l := l))

/-- The S2717 initial identification is a data/instance condition (explicit Prop). -/
def S2711InitialCompatibility (l : PrimeGeFive)
    (initial : SourceDefinition31Data l) : Prop :=
  initial = S1487FaithfulSourceData (l := l)

def s1487QPilotRows : List (String × String) :=
  [ ("S1487SignedLogVolume", "sourceQPilotSignedLog of S1487RootInput.initial") ,
    ("S1487SignedLogVolume_eq_neg_badQ", "PROVED (source scalar identity)") ,
    ("S1487_qPilotVolumeTarget", "PROVED with canonical logQ = 2l*badQAbsLog") ,
    ("signed_volume_eq_of_haar", "PROVED arithmetic reduction of volume_eq") ,
    ("GAP-S2711-INITIAL", "S2711I initial = S1487FaithfulSourceData missing") ,
    ("GAP-HAAR-REGION", "haarLogVolume region = badQAbsLog missing") ,
    ("GAP-THETA-SUBSET", "thetaRegion subset qRegion missing") ]

theorem s1487QPilotRows_length : s1487QPilotRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1S1487QPilotTargetActual