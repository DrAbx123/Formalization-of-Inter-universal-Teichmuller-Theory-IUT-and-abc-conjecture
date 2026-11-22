import tmp.sheaf.xif.paper.S2422MainlineC9Actual
import tmp.sheaf.xif.PaperQPilotObject

/-! # S2440: paper-level C9 source inputs, exactly recorded

This file records the three paper-level C9 inputs isolated by the source audit:
(1) q-pilot scalar normalization `-|log q|`; (2) q-pilot object binding to the
paper/source anchor (trap T5); (3) xi-f output-readout projection/approximation.
It also proves the exact output-readout identity implies the epsilon
approximation and feeds the S2422 C1/hull chain.  No input is fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S2440C9SourceInputsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.C9IUTBridgeOutput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2404QPilotArithmeticActual
open LeanFormal.IUT.XiFPaper.S2422MainlineC9Actual
open LeanFormal.IUT.XiFPaper.S2362MainlineReadoutActual
open OriginalInput
open SourceHodgeTheaterBridge

universe u v w uv upi umon ui ux uy uG

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{u, uv, upi, umon, ui} l V}
variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
variable {P : H2SpokePermutation I}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable [Fintype Label]
variable {W : SourceInternalWiring I R P X Y}
variable {S : SourceP1P2Input (I := I) (R := R) (P := P)
  (X := X) (Y := Y) W}
variable {B : SourceP1P2Bundle W S}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}

noncomputable local instance s2440BadPlacesFintype :
    Fintype I.initial.badPlaces := I.initial.bad_finite

/-! ## 0. Actual q-pilot scalar object from the bad q family -/

theorem s2440_sourceQPilot_eq_neg_bad_sum :
    sourceQPilotSignedLog I.initial =
      -(∑ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)|) := by
  unfold sourceQPilotSignedLog sourceBadQAbsLog
  rfl

/-- Actual q-pilot scalar object built from the actual bad q family. -/
structure S2440ActualQPilotScalarObject where
  badQFamily : I.initial.badPlaces → Real
  badQFamily_eq : ∀ b, badQFamily b = I.initial.reduction.qParameter b
  qPilotLogVolume : Real
  qPilotLogVolume_eq_source :
    qPilotLogVolume = sourceQPilotSignedLog I.initial
  qPilotLogVolume_eq_bad_sum :
    qPilotLogVolume = -(∑ b : I.initial.badPlaces,
      |Real.log (badQFamily b)|)

noncomputable def s2440ActualQPilotScalarObject :
    S2440ActualQPilotScalarObject (I := I) where
  badQFamily := fun b => I.initial.reduction.qParameter b
  badQFamily_eq := fun _ => rfl
  qPilotLogVolume := sourceQPilotSignedLog I.initial
  qPilotLogVolume_eq_source := rfl
  qPilotLogVolume_eq_bad_sum := s2440_sourceQPilot_eq_neg_bad_sum

/-! ## 1. q-pilot scalar normalization -/

/-- Paper-level q-pilot scalar normalization.  The q-pilot object stores the
candidate source scalar; the paper's normalized `-|log q|` must be identified
with the bad-place sum with local factors. -/
structure S2440QPilotScalarNormalizationRequired
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label)
      (Choice := Choice) I G envStrip) where
  paper_log_identification : O.paper_qPilot_log_identification
  paperNormalized : Real
  paperNormalized_eq_bad_sum :
    paperNormalized = -sourceBadQAbsLog I.initial
  candidate_eq_paper :
    sourceQPilotSignedLog I.initial = paperNormalized

/-! ## 2. q-pilot object binding (trap T5) -/

/-- Exact paper-level q-pilot object binding fields. -/
structure S2440QPilotObjectBindingRequired
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label)
      (Choice := Choice) I G envStrip) where
  strip_identification : O.paper_strip_identification
  lineBundle_identification : O.paper_lineBundle_identification
  logKummer_identification : O.paper_logKummer_identification
  qPilot_log_identification : O.paper_qPilot_log_identification

/-! ## 3. xi-f output-readout projection -/

def S2440ProfileReadout
    (b : BridgeOutput (B := B) (R := R)) : Real :=
  R.input.profile.logVolume b.out.source

def S2440XiFExactIdentity
    (b : BridgeOutput (B := B) (R := R)) : Prop :=
  S2440ProfileReadout b = sourceQPilotSignedLog I.initial

/-- Exact output-readout identity (paper xi-f pointwise form). -/
structure S2440XiFReadoutRequired
    (b : BridgeOutput (B := B) (R := R)) where
  exact_identity : S2440XiFExactIdentity b

/-- The exact identity is equivalent to the S2404 arithmetic identity. -/
theorem s2440_exact_iff_S2404
    (b : BridgeOutput (B := B) (R := R)) :
    S2440XiFExactIdentity b ↔ S2404QPilotProfileIdentity b := by
  constructor
  · intro h
    change sourceQPilotSignedLog I.initial =
      s2404CandidateQPilotLogVolume b
    rw [s2404_candidate_eq_out]
    exact h.symm
  · intro h
    change R.input.profile.logVolume b.out.source =
      sourceQPilotSignedLog I.initial
    rw [← s2404_candidate_eq_out]
    exact h.symm

/-- Exact identity gives the S2404 arithmetic input. -/
theorem s2440ArithmeticOfExact
    (b : BridgeOutput (B := B) (R := R))
    (E : S2440XiFReadoutRequired b) :
    S2404QPilotArithmeticRequired b :=
  { arithmetic_identity :=
      (s2440_exact_iff_S2404 b).mp E.exact_identity }

/-- Exact identity implies the epsilon approximation used by the paper's xi-f
"perhaps only up to approximation" language. -/
theorem s2440_exact_implies_approx
    (b : BridgeOutput (B := B) (R := R))
    (E : S2440XiFReadoutRequired b)
    (eps : Real) (heps : 0 ≤ eps) :
    |S2440ProfileReadout b - sourceQPilotSignedLog I.initial| ≤ eps :=
  by
    rw [E.exact_identity, sub_self, abs_zero]
    exact heps

/-- The C1 projection and signed-hull conclusion from the exact xi-f identity. -/
theorem s2440_qPilot_le_hull
    {Xh : Type ux} {p : PaperSignedHull Xh Label}
    {F : S2362FixedCData p}
    (b : BridgeOutput (B := B) (R := R))
    (E : S2440XiFReadoutRequired b)
    (hQ : F.qPilotLogVolume = sourceQPilotSignedLog I.initial) :
    (s2362ReadoutOfProjection
        (s2422C1ProjectionOfArithmetic b
          (s2440ArithmeticOfExact b E) hQ)).Q_C ≤
      p.signedHullLogVolume ∧
    p.ambient.logVolume p.ambient.hull < ⊤ :=
  s2422_qPilot_le_hull_of_arithmetic b
    (s2440ArithmeticOfExact b E) hQ

#check s2440_exact_iff_S2404
#check s2440ArithmeticOfExact
#check s2440_exact_implies_approx
#check s2440_qPilot_le_hull

end LeanFormal.IUT.XiFPaper.S2440C9SourceInputsActual
end
