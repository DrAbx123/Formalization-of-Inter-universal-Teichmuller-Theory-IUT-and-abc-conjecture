import tmp.sheaf.xif.paper.S1447ReportFMarkedTraceActual
import tmp.sheaf.xif.paper.S2362MainlineReadoutActual
import tmp.sheaf.n8.closure.C9IUTBridgeOutput
import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge

/-!
# S2452: paper xi-f output family P_C, nu_C, Q_C and coverage

This file records the paper-level fixed-C output family required by
Corollary 3.12 (xi-e/xi-f), with the exact fields and the scalar consumer.

The current project does not contain the paper final-evaluation family
P_C, its readout nu_C, the exact/signed coverage statement, or the
pointwise profile-readout identification.  C9IUTBridgeOutput explicitly
warns that its bridgePossibleOutputs is the singleton {out}, and S1447
explicitly warns that the value-layer q-mark is not the paper
final-evaluation family.  Neither object is used as P_C here.  The S1447
value-layer readout is sourceQPilotLogVolume, not the paper -|log q|, and
is not used as Q_C here.

What is implemented:

* S2452PaperOutputFamily: the exact paper-family interface, with
  P_C, P_C_nonempty, nu_C, a positive non-unit paper q, Q_C with
  the paper normalization Q_C = -|log q|, the pointwise profile readout
  nu_C D = profile.logVolume D.source, the paper hull upper bound
  nu_C D <= P.signedHullLogVolume (the project's -|log Theta|), and
  exact-or-signed coverage.
* S2452ExactCoverage, S2452SignedCoverage, S2452Coverage: the two
  coverage forms, definitionally the S1447 forms.
* s2452_Q_C_le_of_upper_coverage: the S1447 scalar consumer.  Exact
  coverage gives Q_C <= H by the output witness; signed coverage gives it
  by the midpoint contradiction.  The family specialization is
  S2452PaperOutputFamily.Q_C_le_signedHull.
* S2452PaperOutputFamilyRequired: the proposition that the paper family
  exists.  It has no inhabitant in this file.

No sorry, no axiom, no True/PUnit/empty-type placeholder, no singleton
bridge family, and no value-layer q-mark family are used.  The paper family
and its coverage are recorded as the exact missing source object.

The C9 audit C9-XIE-SOURCE-CONDITION-AUDIT-20261026.md separates the
fixed-q executability condition from output-readout coverage; only the latter,
together with the hull upper bound, yields Q_C <= h_C.  S2362 records the
same missing actual output readout.  S2440 records the paper q-normalization
identification as a separate missing source field; this file does not
identify Q_C with the value-layer source scalar.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2452XiFCoverageActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.C9IUTBridgeOutput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1447MarkedTraceActual
open LeanFormal.IUT.XiFPaper.S2362MainlineReadoutActual

universe u v w ux

/-! ## 1. Exact and signed coverage, and the S1447 scalar consumer -/

/-- Exact output-readout coverage of Q_C by P_C with readout nu_C.
This is definitionally S1447's exact coverage. -/
abbrev S2452ExactCoverage {A : Type*} (P_C : Set A) (nu_C : A → Real)
    (Q_C : Real) : Prop :=
  S1447ExactCoverage P_C nu_C Q_C

/-- Signed-epsilon output-readout coverage of Q_C.  This is definitionally
S1447's signed coverage and is the paper's approximation form. -/
abbrev S2452SignedCoverage {A : Type*} (P_C : Set A) (nu_C : A → Real)
    (Q_C : Real) : Prop :=
  S1447SignedCoverage P_C nu_C Q_C

/-- Exact-or-signed coverage.  This is definitionally S1447's output-readout
projection; it is a proposition, not an axiom or a structure with a proof
field. -/
abbrev S2452Coverage {A : Type*} (P_C : Set A) (nu_C : A → Real)
    (Q_C : Real) : Prop :=
  S1447OutputReadoutProjection P_C nu_C Q_C

/-- Consumer from exact coverage and a uniform upper bound.  This is the
S1447 witness argument, not a new source assumption. -/
theorem s2452_Q_C_le_of_exactCoverage {A : Type*} {P_C : Set A}
    {nu_C : A → Real} {Q_C H : Real}
    (hupper : ∀ D, D ∈ P_C → nu_C D ≤ H)
    (hcover : S2452ExactCoverage P_C nu_C Q_C) : Q_C ≤ H :=
  s1447Comparison_of_exactCoverage hupper
    (show S1447ExactCoverage P_C nu_C Q_C from hcover)

/-- Consumer from signed coverage and a uniform upper bound.  This is the
S1447 midpoint-contradiction argument. -/
theorem s2452_Q_C_le_of_signedCoverage {A : Type*} {P_C : Set A}
    {nu_C : A → Real} {Q_C H : Real}
    (hupper : ∀ D, D ∈ P_C → nu_C D ≤ H)
    (hcover : S2452SignedCoverage P_C nu_C Q_C) : Q_C ≤ H :=
  s1447Comparison_of_signedCoverage hupper
    (show S1447SignedCoverage P_C nu_C Q_C from hcover)

/-- The exact-or-signed coverage consumer: a uniform upper bound plus
coverage of Q_C gives Q_C <= H. -/
theorem s2452_Q_C_le_of_upper_coverage {A : Type*} {P_C : Set A}
    {nu_C : A → Real} {Q_C H : Real}
    (hupper : ∀ D, D ∈ P_C → nu_C D ≤ H)
    (hcover : S2452Coverage P_C nu_C Q_C) : Q_C ≤ H :=
  s1447Comparison_of_outputReadoutProjection hupper
    (show S1447OutputReadoutProjection P_C nu_C Q_C from hcover)

/-! ## 2. The exact paper output family -/

/-- The paper fixed-C output family of Corollary 3.12 (xi-e/xi-f).

The data fields are the paper objects: the restricted final-evaluation
family P_C, a positive non-unit q parameter, its readout nu_C, the
q-pilot scalar Q_C = -|log q|, the pointwise profile-readout equality, the
hull upper bound, and exact-or-signed coverage.  No inhabitant is
constructed; this structure is the exact missing interface. -/
structure S2452PaperOutputFamily
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] [Fintype Label]
    {X : Type ux} (P : PaperSignedHull X Label)
    (R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice) where
  /-- The restricted paper final-evaluation output family, not the singleton
  C9 bridge set and not the value-layer theta-pilot image set. -/
  P_C : Set (ActualOutput R)
  /-- The paper family is nonempty. -/
  P_C_nonempty : P_C.Nonempty
  /-- The fixed paper q parameter, not the S1447 value-layer qMark. -/
  q : Real
  /-- The paper q parameter is positive. -/
  q_pos : 0 < q
  /-- The paper q parameter is not one. -/
  q_ne_one : q ≠ 1
  /-- The output readout, not the S1447 value-layer readout. -/
  nu_C : ActualOutput R → Real
  /-- The paper q-pilot scalar, normalized below as -|log q|. -/
  Q_C : Real
  /-- The paper q-pilot normalization Q_C = -|log q|. -/
  Q_C_eq_neg_abs_log_q : Q_C = -( |Real.log q| )
  /-- The readout is the actual source profile log-volume. -/
  readout_eq : ∀ D, D ∈ P_C → nu_C D =
    R.input.profile.logVolume D.source
  /-- The paper hull upper bound: every output readout is at most the
  signed paper hull log-volume -|log Theta|. -/
  upper : ∀ D, D ∈ P_C → nu_C D ≤ P.signedHullLogVolume
  /-- Exact or signed output-readout coverage of the paper q scalar. -/
  coverage : S2452Coverage P_C nu_C Q_C

namespace S2452PaperOutputFamily

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice] [Fintype Label]
  {X : Type ux} {P : PaperSignedHull X Label}
  {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice}

/-- The paper q scalar is nonpositive. -/
theorem Q_C_nonpos (F : S2452PaperOutputFamily P R) : F.Q_C ≤ 0 := by
  rw [F.Q_C_eq_neg_abs_log_q]
  exact neg_nonpos.mpr (abs_nonneg _)

/-- The family readout is the actual profile readout (S2362/S2396 link). -/
theorem readout_eq_profile (F : S2452PaperOutputFamily P R)
    (D : ActualOutput R) (hD : D ∈ F.P_C) :
    F.nu_C D = R.input.profile.logVolume D.source :=
  F.readout_eq D hD

/-- Every family output's actual profile readout is under the paper signed
hull log-volume. -/
theorem profile_le_signedHull (F : S2452PaperOutputFamily P R)
    (D : ActualOutput R) (hD : D ∈ F.P_C) :
    R.input.profile.logVolume D.source ≤ P.signedHullLogVolume := by
  rw [← F.readout_eq D hD]
  exact F.upper D hD

/-- The paper scalar consumer: Q_C <= -|log Theta|. -/
theorem Q_C_le_signedHull (F : S2452PaperOutputFamily P R) :
    F.Q_C ≤ P.signedHullLogVolume :=
  s2452_Q_C_le_of_upper_coverage F.upper F.coverage

/-- The exact-or-signed coverage field, exposed as the S1447 projection. -/
theorem to_S1447_projection (F : S2452PaperOutputFamily P R) :
    S1447OutputReadoutProjection F.P_C F.nu_C F.Q_C :=
  show S1447OutputReadoutProjection F.P_C F.nu_C F.Q_C from F.coverage

end S2452PaperOutputFamily

/-! ## 3. The exact missing record -/

/-- The exact missing paper output family.  The proposition has no inhabitant
in this file: no paper P_C, no nu_C, no exact/signed coverage, and no
paper q-normalization identification are constructed.  Its exact fields are
those of S2452PaperOutputFamily:

* P_C : Set (ActualOutput R) and P_C_nonempty;
* q : Real, q_pos : 0 < q, q_ne_one : q != 1;
* nu_C : ActualOutput R -> Real;
* Q_C : Real with Q_C = -|log q|;
* readout_eq : forall D in P_C, nu_C D = profile.logVolume D.source;
* upper : forall D in P_C, nu_C D <= P.signedHullLogVolume;
* coverage : exact or signed coverage of Q_C. -/
abbrev S2452PaperOutputFamilyRequired
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] [Fintype Label]
    {X : Type ux} (P : PaperSignedHull X Label)
    (R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice) : Prop :=
  Nonempty (S2452PaperOutputFamily P R)

/-- Conditional consumer from the exact missing record.  The hypothesis is
never constructed here. -/
theorem s2452_Q_C_le_signedHull_of_required
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] [Fintype Label]
    {X : Type ux} {P : PaperSignedHull X Label}
    {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice}
    (h : S2452PaperOutputFamilyRequired P R) :
    ∃ F : S2452PaperOutputFamily P R,
      F.Q_C ≤ P.signedHullLogVolume := by
  classical
  have h' : Nonempty (S2452PaperOutputFamily P R) := h
  let F : S2452PaperOutputFamily P R := Classical.choice h'
  exact ⟨F, F.Q_C_le_signedHull⟩

/-! ## 4. S2362 consumer: the fixed-C q scalar under the paper hull -/

/-- If the paper family scalar is the fixed-C q-pilot scalar of S2362, then the
S2362 scalar is under the paper signed hull log-volume.  This uses the family
upper bound, not S2362FixedCData.xi_f_inequality. -/
theorem s2452_fixedC_qPilot_le_signedHull
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] [Fintype Label]
    {X : Type ux} {P : PaperSignedHull X Label}
    {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice}
    (F : S2452PaperOutputFamily P R) (C : S2362FixedCData P)
    (hQ : F.Q_C = C.qPilotLogVolume) :
    C.qPilotLogVolume ≤ P.signedHullLogVolume := by
  rw [← hQ]
  exact F.Q_C_le_signedHull

/-- The S2362 scalar package from the paper family: the comparison and
finiteness of the paper hull log-volume. -/
theorem s2452_fixedC_mainline
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] [Fintype Label]
    {X : Type ux} {P : PaperSignedHull X Label}
    {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice}
    (F : S2452PaperOutputFamily P R) (C : S2362FixedCData P)
    (hQ : F.Q_C = C.qPilotLogVolume) :
    C.qPilotLogVolume ≤ P.signedHullLogVolume ∧
      P.ambient.logVolume P.ambient.hull < ⊤ :=
  ⟨s2452_fixedC_qPilot_le_signedHull F C hQ,
    P.ambient_hull_logVolume_lt_top⟩

/-! ## Status

* The coverage definitions and the exact/signed consumer are proved and are
  definitionally the S1447 logic.
* S2452PaperOutputFamily is an interface, not a construction.  The paper
  P_C, nu_C, coverage, and q-normalization are absent from the tree.
* S2452PaperOutputFamilyRequired has no inhabitant.
* The singleton C9 bridge and the S1447 value-layer q-mark are not used as the
  paper family.
* This file was not compiled (serial build hold): statement compilation and
  proof checking are unverified.
-/

#check S2452ExactCoverage
#check S2452SignedCoverage
#check S2452Coverage
#check s2452_Q_C_le_of_exactCoverage
#check s2452_Q_C_le_of_signedCoverage
#check s2452_Q_C_le_of_upper_coverage
#check S2452PaperOutputFamily
#check S2452PaperOutputFamily.Q_C_eq_neg_abs_log_q
#check S2452PaperOutputFamily.Q_C
#check S2452PaperOutputFamily.Q_C_nonpos
#check S2452PaperOutputFamily.readout_eq_profile
#check S2452PaperOutputFamily.profile_le_signedHull
#check S2452PaperOutputFamily.Q_C_le_signedHull
#check S2452PaperOutputFamilyRequired
#check s2452_Q_C_le_signedHull_of_required
#check s2452_fixedC_qPilot_le_signedHull
#check s2452_fixedC_mainline

end LeanFormal.IUT.XiFPaper.S2452XiFCoverageActual

end
