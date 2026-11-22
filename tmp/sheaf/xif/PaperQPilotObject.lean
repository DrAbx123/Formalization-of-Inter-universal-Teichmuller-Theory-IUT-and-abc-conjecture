import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceQSideComparison
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ContractSourceReduction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import tmp.sheaf.xif.paper.PaperLineBundleCarrierBase

/-! # Paper-level q-pilot object: exact source structures and obligations

**STATUS: structure/obligation file, not a construction of the paper q-pilot.**
This file defines the exact object surface that the paper's `(1,0)` q-pilot
would have to inhabit, using the actual source declarations in
`SourceArithmeticHolomorphicLanding.lean`, `SourceKummerEvaluationArrows.lean`,
`SourceQSideComparison.lean`, and `ContractSourceReduction.lean`. It does not
reuse the value-layer theta-label-1 surrogate (`sourceQPilotPoint`).

## What is actual here

* `sourceQPilotSignedLog`: the negative sum of `|log q_b|` over the actual bad
  q-parameters of `SourceDefinition31Data`. This is an actual source scalar
  candidate, but it is NOT identified with the paper q-pilot log-volume.
* `PaperQPilotObject`: fields carrying the actual source q-pilot strip anchor
  (`sourceQPilotStrip`), the actual one-column arithmetic holomorphic structure
  (Card AS), the actual reduced arithmetic vector-bundle carrier (Card AV), and
  an actual reduced Kummer arrow (`SourceKummerArrow`).

## Exact missing paper objects (recorded as obligation fields)

1. `sourceQPilotStrip` is explicitly only the input Hodge theater's `F`-layer
   strip; it is NOT asserted to be the paper's q-pilot
   `F^boxplus-triangleright-x-mu`-prime-strip, the `x`-mu layer, or the
   `(1,0)`-level object (see its own docstring). `paper_strip_identification`
   is the exact missing identification.
2. `SourceArithmeticVectorBundle` is a reduced section/localization carrier;
   rank, integrality, arithmetic line-bundle structure and Frobenioid theory
   are not modeled. `paper_lineBundle_identification` is the missing
   arithmetic-line-bundle/rank-one identification.
3. `SourceKummerArrow` is the reduced source interface for the Kummer arrow,
   not the paper's log-Kummer representation of the q-pilot on `1,circ U_Q`.
   `paper_logKummer_identification` is the missing map/identification.
4. The paper q-pilot log-volume `-|log q|` requires the procession-normalized
   q-pilot measure on the actual q-pilot object, not just the sum of bad
   q-parameter absolute logs. `paper_qPilot_log_identification` records this
   exact gap; the scalar lemmas below only bound the actual candidate.
5. The `(1,0)` label binding and the `1,circ` column identification are absent.

No `sorry`, no axiom, no toy witness is used. No `Nonempty PaperQPilotObject`
is asserted; the structure may have no inhabitant until the source
identifications above are constructed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT
namespace Theorem311Source

universe ua uv upi umon ui uG uL uC

variable {l : PrimeGeFive}

/-- The actual source scalar candidate for the absolute q-pilot log-volume: the
sum over the actual bad q-parameters of `|log q_b|`. This is not asserted to be
the paper's `|log q|`; see the module docstring. -/
noncomputable def sourceBadQAbsLog (S : SourceDefinition31Data l) : Real :=
  letI := S.bad_finite
  ∑ b : S.badPlaces, |Real.log (S.reduction.qParameter b)|

/-- The actual source scalar candidate for the signed q-pilot log-volume:
`- sum_b |log q_b|`. This is negative or zero, but it is not asserted to be
the paper's `-|log q|`. -/
noncomputable def sourceQPilotSignedLog (S : SourceDefinition31Data l) : Real :=
  -sourceBadQAbsLog S

theorem sourceBadQAbsLog_nonneg (S : SourceDefinition31Data l) :
    0 ≤ sourceBadQAbsLog S := by
  unfold sourceBadQAbsLog
  letI := S.bad_finite
  exact Finset.sum_nonneg (fun b _ => abs_nonneg _)

theorem sourceQPilotSignedLog_nonpos (S : SourceDefinition31Data l) :
    sourceQPilotSignedLog S ≤ 0 := by
  unfold sourceQPilotSignedLog
  exact neg_nonpos.mpr (sourceBadQAbsLog_nonneg S)

theorem sourceBadQAbsLog_pos_of_nonempty (S : SourceDefinition31Data l)
    (hbad : Nonempty S.badPlaces) : 0 < sourceBadQAbsLog S := by
  unfold sourceBadQAbsLog
  letI := S.bad_finite
  obtain ⟨b⟩ := hbad
  refine Finset.sum_pos' (fun b _ => abs_nonneg _) ⟨b, Finset.mem_univ _, ?_⟩
  apply abs_pos.mpr
  apply Real.log_ne_zero.mpr
  refine ⟨S.reduction.qParameter_nonzero b, ?_, ?_⟩
  · exact S.reduction.qParameter_reduction_compatibility b
      (S.reduction.stableReduction_proved b)
  · intro hneg
    have hcontr := S.reduction.qParameter_contracting b
    rw [hneg, norm_neg, norm_one] at hcontr
    linarith

theorem sourceQPilotSignedLog_neg_of_nonempty (S : SourceDefinition31Data l)
    (hbad : Nonempty S.badPlaces) : sourceQPilotSignedLog S < 0 := by
  unfold sourceQPilotSignedLog
  exact neg_neg_of_pos (sourceBadQAbsLog_pos_of_nonempty S hbad)

/-- The paper-level q-pilot object surface. Every field is an actual source
structure or the actual source q-log candidate; the `paper_*_identification`
fields are the exact missing source obligations, not assumptions proved here. -/
structure PaperQPilotObject
    {l : PrimeGeFive} {V : Type uv}
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (G : Type uG) [Group G] [TopologicalSpace G]
    (envStrip : FPrimeStrip V) where
  /-- The actual source input boundary used by `sourceQPilotStrip`. -/
  boundary : SourceProcessionBoundary.Input.{ua, uv, upi, umon, uL, uC}
    (l := l) (V := V) (Label := Label) (Choice := Choice)
  /-- The actual `F`-layer source strip anchor. -/
  strip : FPrimeStrip V
  strip_eq_source : strip = sourceQPilotStrip boundary
  /-- Card AS: the actual one-column arithmetic holomorphic structure. -/
  oneColumn : SourceOneColumnArithmeticHolomorphicStructure V
  /-- Card AV: the actual reduced arithmetic vector-bundle carrier. -/
  lineBundle : LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual.PaperLineBundleCarrier
    (k := I.initial.arithmetic.Fmod)
  /-- The actual reduced Kummer arrow interface. -/
  logKummer : SourceKummerArrow G envStrip strip
  /-- The actual source scalar candidate for the q-pilot log-volume. -/
  qPilotLogVolume : Real
  qPilotLogVolume_eq : qPilotLogVolume = sourceQPilotSignedLog I.initial
  /-- Missing: strip is the paper's q-pilot `(1,0)` `F^...`-prime-strip. -/
  paper_strip_identification : Prop
  /-- Missing: the reduced bundle is the paper's rank-one arithmetic line
  bundle giving rise to the q-pilot. -/
  paper_lineBundle_identification : Prop
  /-- Missing: the reduced Kummer arrow is the paper's log-Kummer
  representation of the q-pilot on `1,circ U_Q`. -/
  paper_logKummer_identification : Prop
  /-- Missing: the scalar is the paper's procession-normalized `-|log q|`. -/
  paper_qPilot_log_identification : Prop

namespace PaperQPilotObject

variable {V : Type uv} {Label : Type uL} {Choice : Type uC}
  [AddGroup Label] [Preorder Choice]
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
  {G : Type uG} [Group G] [TopologicalSpace G]
  {envStrip : FPrimeStrip V}

theorem strip_eq (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) :
    O.strip = sourceQPilotStrip O.boundary := O.strip_eq_source

theorem qPilotLogVolume_eq_neg_abs_sum
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) :
    O.qPilotLogVolume = -sourceBadQAbsLog I.initial := by
  rw [O.qPilotLogVolume_eq]
  rfl

theorem qPilotLogVolume_nonpos (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) :
    O.qPilotLogVolume ≤ 0 := by
  rw [O.qPilotLogVolume_eq]
  exact sourceQPilotSignedLog_nonpos I.initial

theorem qPilotLogVolume_neg_of_bad_nonempty
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (hbad : Nonempty I.initial.badPlaces) :
    O.qPilotLogVolume < 0 := by
  rw [O.qPilotLogVolume_eq]
  exact sourceQPilotSignedLog_neg_of_nonempty I.initial hbad

end PaperQPilotObject

end Theorem311Source
end LeanFormal.IUT

end
