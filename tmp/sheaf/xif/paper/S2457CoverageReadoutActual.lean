import tmp.sheaf.xif.paper.S2452XiFCoverageActual
import tmp.sheaf.xif.paper.S2362MainlineReadoutActual
import tmp.sheaf.xif.paper.S1447ReportFMarkedTraceActual

/-!
# S2457: actual paper coverage/readout consumption

This file consumes the paper fixed-C output interface of S2452 and the
fixed-C scalar of S2362.  It adds pure logic only; it does not construct the
paper final-evaluation family.

What is proved:

* Coverage from an actual output witness.  The witness records
  S2457ExactOutputWitness, S2457OneSidedOutputWitness and
  S2457ApproxOutputWitness are generic in the output carrier A, the candidate
  family P_C, the readout nu_C and the target Q_C.  An exact witness gives
  exact coverage, hence signed coverage; a one-sided witness gives signed
  coverage; a single epsilon witness gives only the weakened bound
  Q_C <= H + eps.  No paper-family assumption is used in this section.

* Paper-family consumption.  A uniform upper bound plus exact-or-signed
  coverage gives Q_C <= H.  For the S2452 family the coverage is its
  coverage field and the bound is Q_C <= -|log Theta|; the generic step is
  S2452's s2452_Q_C_le_of_upper_coverage, which is the S1447 witness/midpoint
  argument.  The same bound is derived inside S2452PaperOutputFamily from an
  explicit exact output witness.

* S2362 connection.  s2457FixedCDataOfPaperFamily builds S2362FixedCData from
  the paper family with the S2362 xi_f_inequality field proved from the paper
  coverage and hull upper bound, not assumed.  Exact paper coverage also
  builds the S2362 C1 output-readout projection and readout on the actual
  Theorem 3.11 output carrier, so the S2362 mainline scalar applies.

* Exact missing record.  S2457PaperCoverageRequired is the exact missing
  paper-family coverage record.  It is definitionally S2452's paper-family
  requirement, whose coverage field is the exact/signed coverage.  No
  inhabitant is constructed in this file.

No fake object is used: the C9 singleton bridgePossibleOutputs, the S1447
value-layer q-mark/readout, and arbitrary output types are not used as the
paper family.  The S1447 value-layer witness inhabits the generic witness
structures at the value layer only; it is not the paper final-evaluation
family and it is not used to construct S2457PaperCoverageRequired.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2457CoverageReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C9IUTBridgeOutput
open LeanFormal.IUT.XiFPaper.S1447MarkedTraceActual
open LeanFormal.IUT.XiFPaper.S2362MainlineReadoutActual
open LeanFormal.IUT.XiFPaper.S2452XiFCoverageActual

universe u v w ux

/-! ## 1. Actual output witnesses and exact/signed coverage

The structures below are witness records, not paper-family data: A, P_C,
nu_C and Q_C are arbitrary.  They construct the coverage propositions of
S2452/S1447 from explicit output data. -/

/-- An exact actual-output witness: an output D in the candidate family P_C
whose readout is exactly Q_C. -/
structure S2457ExactOutputWitness {A : Type*} (P_C : Set A)
    (nu_C : A -> Real) (Q_C : Real) where
  /-- The actual output. -/
  D : A
  /-- The output lies in the candidate family. -/
  D_mem : D ∈ P_C
  /-- Its readout is exactly the target scalar. -/
  readout_eq : nu_C D = Q_C

/-- A one-sided (signed) actual-output witness: an output in the candidate
family whose readout already dominates Q_C.  This is stronger than the
all-epsilon signed coverage of S1447, which it implies. -/
structure S2457OneSidedOutputWitness {A : Type*} (P_C : Set A)
    (nu_C : A -> Real) (Q_C : Real) where
  D : A
  D_mem : D ∈ P_C
  le_readout : Q_C ≤ nu_C D

/-- A single epsilon-approximate actual-output witness.  One such witness does
not give exact or signed coverage; it gives the weakened comparison
Q_C <= H + eps against a uniform upper bound H. -/
structure S2457ApproxOutputWitness {A : Type*} (P_C : Set A)
    (nu_C : A -> Real) (Q_C : Real) where
  eps : Real
  eps_pos : 0 < eps
  D : A
  D_mem : D ∈ P_C
  approx : Q_C - eps ≤ nu_C D

/-- Exact coverage is exactly the existence of an exact actual-output witness. -/
theorem s2457_exactCoverage_iff_witness {A : Type*} {P_C : Set A}
    {nu_C : A -> Real} {Q_C : Real} :
    S2452ExactCoverage P_C nu_C Q_C ↔
      Nonempty (S2457ExactOutputWitness P_C nu_C Q_C) := by
  constructor
  · intro h
    obtain ⟨D, hD, hDQ⟩ := h
    exact ⟨⟨D, hD, hDQ⟩⟩
  · intro h
    obtain ⟨W⟩ := h
    exact ⟨W.D, W.D_mem, W.readout_eq⟩

/-- An exact actual-output witness constructs exact coverage. -/
theorem s2457_exactCoverage_of_witness {A : Type*} {P_C : Set A}
    {nu_C : A -> Real} {Q_C : Real}
    (W : S2457ExactOutputWitness P_C nu_C Q_C) :
    S2452ExactCoverage P_C nu_C Q_C :=
  ⟨W.D, W.D_mem, W.readout_eq⟩

/-- An exact actual-output witness constructs exact-or-signed coverage. -/
theorem s2457_coverage_of_witness {A : Type*} {P_C : Set A}
    {nu_C : A -> Real} {Q_C : Real}
    (W : S2457ExactOutputWitness P_C nu_C Q_C) :
    S2452Coverage P_C nu_C Q_C :=
  Or.inl (s2457_exactCoverage_of_witness W)

/-- Exact coverage implies signed coverage: the exact witness satisfies every
epsilon lower bound. -/
theorem s2457_signedCoverage_of_exactCoverage {A : Type*} {P_C : Set A}
    {nu_C : A -> Real} {Q_C : Real}
    (h : S2452ExactCoverage P_C nu_C Q_C) :
    S2452SignedCoverage P_C nu_C Q_C := by
  intro eps heps
  obtain ⟨D, hD, hDQ⟩ := h
  refine ⟨D, hD, ?_⟩
  rw [hDQ]
  linarith

/-- A one-sided actual-output witness constructs signed coverage. -/
theorem s2457_signedCoverage_of_oneSidedWitness {A : Type*} {P_C : Set A}
    {nu_C : A -> Real} {Q_C : Real}
    (W : S2457OneSidedOutputWitness P_C nu_C Q_C) :
    S2452SignedCoverage P_C nu_C Q_C := by
  intro eps heps
  refine ⟨W.D, W.D_mem, ?_⟩
  linarith [W.le_readout]

/-! ## 2. Pure-logic consumption: uniform upper bound plus coverage -/

/-- Uniform upper bound plus exact coverage gives Q_C <= H; this is S2452's
restatement of the S1447 witness argument. -/
theorem s2457_Q_C_le_of_upper_exact {A : Type*} {P_C : Set A}
    {nu_C : A -> Real} {Q_C H : Real}
    (hupper : ∀ D, D ∈ P_C -> nu_C D ≤ H)
    (hcover : S2452ExactCoverage P_C nu_C Q_C) : Q_C ≤ H :=
  s2452_Q_C_le_of_exactCoverage hupper hcover

/-- Uniform upper bound plus signed coverage gives Q_C <= H; this is S2452's
restatement of the S1447 midpoint contradiction. -/
theorem s2457_Q_C_le_of_upper_signed {A : Type*} {P_C : Set A}
    {nu_C : A -> Real} {Q_C H : Real}
    (hupper : ∀ D, D ∈ P_C -> nu_C D ≤ H)
    (hcover : S2452SignedCoverage P_C nu_C Q_C) : Q_C ≤ H :=
  s2452_Q_C_le_of_signedCoverage hupper hcover

/-- The exact-or-signed coverage consumer: a uniform upper bound plus coverage
of Q_C gives Q_C <= H.  This is the S2452/S1447 scalar step. -/
theorem s2457_Q_C_le_of_upper_coverage {A : Type*} {P_C : Set A}
    {nu_C : A -> Real} {Q_C H : Real}
    (hupper : ∀ D, D ∈ P_C -> nu_C D ≤ H)
    (hcover : S2452Coverage P_C nu_C Q_C) : Q_C ≤ H :=
  s2452_Q_C_le_of_upper_coverage hupper hcover

/-- Uniform upper bound plus an exact actual-output witness. -/
theorem s2457_Q_C_le_of_upper_witness {A : Type*} {P_C : Set A}
    {nu_C : A -> Real} {Q_C H : Real}
    (hupper : ∀ D, D ∈ P_C -> nu_C D ≤ H)
    (W : S2457ExactOutputWitness P_C nu_C Q_C) : Q_C ≤ H :=
  s2457_Q_C_le_of_upper_exact hupper (s2457_exactCoverage_of_witness W)

/-- Uniform upper bound plus a one-sided actual-output witness. -/
theorem s2457_Q_C_le_of_upper_oneSidedWitness {A : Type*} {P_C : Set A}
    {nu_C : A -> Real} {Q_C H : Real}
    (hupper : ∀ D, D ∈ P_C -> nu_C D ≤ H)
    (W : S2457OneSidedOutputWitness P_C nu_C Q_C) : Q_C ≤ H :=
  calc
    Q_C ≤ nu_C W.D := W.le_readout
    _ ≤ H := hupper W.D W.D_mem

/-- A single epsilon-approximate witness gives only the epsilon-weakened bound
Q_C <= H + eps; it does not give Q_C <= H. -/
theorem s2457_Q_C_le_add_eps_of_approxWitness {A : Type*} {P_C : Set A}
    {nu_C : A -> Real} {Q_C H : Real}
    (hupper : ∀ D, D ∈ P_C -> nu_C D ≤ H)
    (W : S2457ApproxOutputWitness P_C nu_C Q_C) :
    Q_C ≤ H + W.eps := by
  have h : Q_C - W.eps ≤ H := le_trans W.approx (hupper W.D W.D_mem)
  linarith

/-! ## 3. Paper-family consumption (S2452 fields, S1447 logic) -/

section PaperFamily

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice] [Fintype Label]
  {X : Type ux} {P : PaperSignedHull X Label}
  {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization.{u, v, w} l Label Choice}

/-- Uniform upper bound plus the paper family's exact-or-signed coverage field,
with an arbitrary target H. -/
theorem s2457_paper_Q_C_le_of_upper_coverage
    (F : S2452PaperOutputFamily P R) {H : Real}
    (hupper : ∀ D, D ∈ F.P_C -> F.nu_C D ≤ H) : F.Q_C ≤ H :=
  s2452_Q_C_le_of_upper_coverage hupper F.coverage

/-- Uniform upper bound plus an explicit exact-coverage hypothesis for the
paper family. -/
theorem s2457_paper_Q_C_le_of_upper_exact
    (F : S2452PaperOutputFamily P R) {H : Real}
    (hupper : ∀ D, D ∈ F.P_C -> F.nu_C D ≤ H)
    (hexact : S2452ExactCoverage F.P_C F.nu_C F.Q_C) : F.Q_C ≤ H :=
  s2452_Q_C_le_of_exactCoverage hupper hexact

/-- Uniform upper bound plus an explicit signed-coverage hypothesis for the
paper family. -/
theorem s2457_paper_Q_C_le_of_upper_signed
    (F : S2452PaperOutputFamily P R) {H : Real}
    (hupper : ∀ D, D ∈ F.P_C -> F.nu_C D ≤ H)
    (hsigned : S2452SignedCoverage F.P_C F.nu_C F.Q_C) : F.Q_C ≤ H :=
  s2452_Q_C_le_of_signedCoverage hupper hsigned

/-- Uniform upper bound plus an exact output witness inside the paper family.
Only the witness is supplied; the family's coverage field is not used. -/
theorem s2457_paper_Q_C_le_of_upper_witness
    (F : S2452PaperOutputFamily P R) {H : Real}
    (hupper : ∀ D, D ∈ F.P_C -> F.nu_C D ≤ H)
    (W : S2457ExactOutputWitness F.P_C F.nu_C F.Q_C) : F.Q_C ≤ H :=
  s2457_Q_C_le_of_upper_coverage hupper (s2457_coverage_of_witness W)

/-- The paper-family scalar is under the paper signed hull log-volume
-|log Theta|, using the family upper bound and coverage field. -/
theorem s2457_paper_Q_C_le_signedHull
    (F : S2452PaperOutputFamily P R) :
    F.Q_C ≤ P.signedHullLogVolume :=
  s2452_Q_C_le_of_upper_coverage F.upper F.coverage

/-- Exact coverage of the paper family gives the signed-hull bound through the
family's own uniform upper bound. -/
theorem s2457_paper_Q_C_le_signedHull_of_exact
    (F : S2452PaperOutputFamily P R)
    (hexact : S2452ExactCoverage F.P_C F.nu_C F.Q_C) :
    F.Q_C ≤ P.signedHullLogVolume :=
  s2452_Q_C_le_of_exactCoverage F.upper hexact

/-- Signed coverage of the paper family gives the signed-hull bound through the
family's own uniform upper bound. -/
theorem s2457_paper_Q_C_le_signedHull_of_signed
    (F : S2452PaperOutputFamily P R)
    (hsigned : S2452SignedCoverage F.P_C F.nu_C F.Q_C) :
    F.Q_C ≤ P.signedHullLogVolume :=
  s2452_Q_C_le_of_signedCoverage F.upper hsigned

/-- The paper-family readout is the actual source profile log-volume. -/
theorem s2457_paper_readout_eq_profile
    (F : S2452PaperOutputFamily P R) (D : ActualOutput R)
    (hD : D ∈ F.P_C) :
    F.nu_C D = R.input.profile.logVolume D.source :=
  F.readout_eq D hD

/-- Every paper-family output's actual profile readout is under the paper
signed hull log-volume. -/
theorem s2457_paper_profile_le_signedHull
    (F : S2452PaperOutputFamily P R) (D : ActualOutput R)
    (hD : D ∈ F.P_C) :
    R.input.profile.logVolume D.source ≤ P.signedHullLogVolume := by
  rw [← F.readout_eq D hD]
  exact F.upper D hD

/-- The paper-family coverage is the S1447 output-readout projection. -/
theorem s2457_paper_to_S1447
    (F : S2452PaperOutputFamily P R) :
    S1447OutputReadoutProjection F.P_C F.nu_C F.Q_C :=
  show S1447OutputReadoutProjection F.P_C F.nu_C F.Q_C from F.coverage

/-- An exact output witness for the paper family's own data constructs its
exact-or-signed coverage.  This does not construct the paper family itself. -/
theorem s2457_paper_coverage_of_witness
    (F : S2452PaperOutputFamily P R)
    (W : S2457ExactOutputWitness F.P_C F.nu_C F.Q_C) :
    S2452Coverage F.P_C F.nu_C F.Q_C :=
  s2457_coverage_of_witness W

/-! ## 4. S2362 fixed-C scalar connection -/

/-- The S2362 fixed-C data built from the paper family.  The S2362
xi_f_inequality field is proved from the paper family's coverage and hull
upper bound, not assumed; the q-pilot field is the paper Q_C. -/
noncomputable def s2457FixedCDataOfPaperFamily
    (F : S2452PaperOutputFamily P R) : S2362FixedCData P where
  qPilotLogVolume := F.Q_C
  qPilotLogVolume_eq_neg_abs := (F.Q_C = -( |Real.log F.q| ))
  xi_f_inequality := s2457_paper_Q_C_le_signedHull F

/-- The constructed fixed-C q-pilot scalar is the paper q-pilot scalar. -/
theorem s2457FixedCData_qPilotLogVolume
    (F : S2452PaperOutputFamily P R) :
    (s2457FixedCDataOfPaperFamily F).qPilotLogVolume = F.Q_C :=
  rfl

/-- The constructed fixed-C scalar is under the paper signed hull: the S2362
inequality field is discharged by the paper family. -/
theorem s2457_fixedC_scalar_of_paperFamily
    (F : S2452PaperOutputFamily P R) :
    (s2457FixedCDataOfPaperFamily F).qPilotLogVolume ≤
      P.signedHullLogVolume :=
  (s2457FixedCDataOfPaperFamily F).xi_f_inequality

/-- The S2362 mainline scalar from the constructed fixed-C data: comparison and
hull finiteness. -/
theorem s2457_fixedC_mainline_of_paperFamily
    (F : S2452PaperOutputFamily P R) :
    (s2457FixedCDataOfPaperFamily F).qPilotLogVolume ≤
        P.signedHullLogVolume ∧
      P.ambient.logVolume P.ambient.hull < ⊤ :=
  ⟨(s2457FixedCDataOfPaperFamily F).xi_f_inequality,
    P.ambient_hull_logVolume_lt_top⟩

/-- General fixed-C scalar connection: if the S2362 scalar is the paper family
scalar, then the S2362 scalar is under the paper signed hull.  This is S2452's
theorem, restated as the S2457 interface. -/
theorem s2457_fixedC_qPilot_le_signedHull
    (F : S2452PaperOutputFamily P R) (C : S2362FixedCData P)
    (hQ : F.Q_C = C.qPilotLogVolume) :
    C.qPilotLogVolume ≤ P.signedHullLogVolume :=
  s2452_fixedC_qPilot_le_signedHull F C hQ

/-- An S2362 actual output readout whose scalar is the paper scalar is under the
paper signed hull, by the paper family rather than by the readout data. -/
theorem s2457_fixedC_readout_eq_paper
    (F : S2452PaperOutputFamily P R) (C : S2362FixedCData P)
    (hQ : F.Q_C = C.qPilotLogVolume)
    (W : S2362ActualOutputReadout P C) :
    W.Q_C = F.Q_C :=
  W.Q_C_eq_qPilot.trans hQ.symm

/-- The same readout is under the paper signed hull. -/
theorem s2457_fixedC_readout_le_signedHull
    (F : S2452PaperOutputFamily P R) (C : S2362FixedCData P)
    (hQ : F.Q_C = C.qPilotLogVolume)
    (W : S2362ActualOutputReadout P C) :
    W.Q_C ≤ P.signedHullLogVolume := by
  rw [s2457_fixedC_readout_eq_paper F C hQ W]
  exact s2457_paper_Q_C_le_signedHull F

/-- Exact paper coverage builds the S2362 C1 output-readout projection on the
actual Theorem 3.11 output carrier, with the paper family's own P_C and nu_C.
Signed-only coverage does not supply the required exact member. -/
noncomputable def s2457S2362ProjectionOfExactPaperFamily
    (F : S2452PaperOutputFamily P R)
    (hexact : S2452ExactCoverage F.P_C F.nu_C F.Q_C) :
    S2362C1OutputReadoutProjectionRequired P
      (s2457FixedCDataOfPaperFamily F) where
  Output := ActualOutput R
  P_C := F.P_C
  nu_C := F.nu_C
  Q_C := F.Q_C
  Q_C_eq_qPilot := rfl
  exists_output := hexact

/-- The S2362 actual output readout obtained from exact paper coverage by
choice. -/
noncomputable def s2457S2362ReadoutOfExactPaperFamily
    (F : S2452PaperOutputFamily P R)
    (hexact : S2452ExactCoverage F.P_C F.nu_C F.Q_C) :
    S2362ActualOutputReadout P (s2457FixedCDataOfPaperFamily F) :=
  s2362ReadoutOfProjection (s2457S2362ProjectionOfExactPaperFamily F hexact)

/-- The S2362 readout's scalar is the paper scalar. -/
theorem s2457S2362Readout_Q_C_eq_paper
    (F : S2452PaperOutputFamily P R)
    (hexact : S2452ExactCoverage F.P_C F.nu_C F.Q_C) :
    (s2457S2362ReadoutOfExactPaperFamily F hexact).Q_C = F.Q_C :=
  rfl

/-- The S2362 readout scalar is under the paper signed hull, by S2362's own
scalar step applied to the constructed readout. -/
theorem s2457S2362Readout_le_signedHull
    (F : S2452PaperOutputFamily P R)
    (hexact : S2452ExactCoverage F.P_C F.nu_C F.Q_C) :
    (s2457S2362ReadoutOfExactPaperFamily F hexact).Q_C ≤
      P.signedHullLogVolume :=
  s2362_qPilot_le_hull (s2457S2362ReadoutOfExactPaperFamily F hexact)

/-- The S2362 mainline scalar from exact paper coverage. -/
theorem s2457S2362_mainline_of_exactPaperFamily
    (F : S2452PaperOutputFamily P R)
    (hexact : S2452ExactCoverage F.P_C F.nu_C F.Q_C) :
    (s2457S2362ReadoutOfExactPaperFamily F hexact).Q_C ≤
        P.signedHullLogVolume ∧
      P.ambient.logVolume P.ambient.hull < ⊤ :=
  s2362_mainline_scalar (s2457S2362ReadoutOfExactPaperFamily F hexact)

end PaperFamily

/-! ## 5. The exact missing paper-family coverage record -/

/-- The exact missing paper-family coverage record.

This is definitionally S2452's S2452PaperOutputFamilyRequired
(Nonempty (S2452PaperOutputFamily P R)).  Its fields are the paper fixed-C
output data together with exact-or-signed coverage:

* P_C : Set (ActualOutput R) and P_C_nonempty;
* q : Real, q_pos : 0 < q, q_ne_one : q != 1;
* nu_C : ActualOutput R -> Real;
* Q_C : Real with Q_C = -|log q|;
* readout_eq : forall D in P_C, nu_C D = profile.logVolume D.source;
* upper : forall D in P_C, nu_C D <= P.signedHullLogVolume;
* coverage : exact or signed coverage of Q_C.

The coverage field is exactly the missing paper-family coverage.  No inhabitant
of this record is constructed in this file: no paper P_C, no paper nu_C and no
paper coverage are supplied, and the S1447 value-layer witness and the C9
singleton are not used as a substitute. -/
abbrev S2457PaperCoverageRequired
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] [Fintype Label]
    {X : Type ux} (P : PaperSignedHull X Label)
    (R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization.{u, v, w} l Label Choice) : Prop :=
  Nonempty (S2452PaperOutputFamily P R)

section PaperCoverage

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice] [Fintype Label]
  {X : Type ux} {P : PaperSignedHull X Label}
  {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization.{u, v, w} l Label Choice}

/-- The record is literally the S2452 paper-family requirement. -/
theorem s2457_paperCoverageRequired_iff_s2452Required :
    S2457PaperCoverageRequired P R ↔
      S2452PaperOutputFamilyRequired P R :=
  Iff.rfl

/-- The record entails an actual paper family whose coverage field is the
exact-or-signed paper coverage. -/
theorem s2457_paperCoverageRequired_iff_exists_family_coverage :
    S2457PaperCoverageRequired P R ↔
      ∃ F : S2452PaperOutputFamily P R,
        S2452Coverage F.P_C F.nu_C F.Q_C := by
  constructor
  · intro h
    obtain ⟨F⟩ := h
    exact ⟨F, F.coverage⟩
  · intro h
    obtain ⟨F, _⟩ := h
    exact ⟨F⟩

/-- Conditional consumer from the exact missing record: the paper-family
coverage gives a paper scalar under the paper signed hull.  The hypothesis is
never constructed here. -/
theorem s2457_Q_C_le_signedHull_of_paperCoverageRequired
    (h : S2457PaperCoverageRequired P R) :
    ∃ F : S2452PaperOutputFamily P R,
      F.Q_C ≤ P.signedHullLogVolume :=
  s2452_Q_C_le_signedHull_of_required h

/-- Conditional consumer with hull finiteness. -/
theorem s2457_mainline_of_paperCoverageRequired
    (h : S2457PaperCoverageRequired P R) :
    ∃ F : S2452PaperOutputFamily P R,
      F.Q_C ≤ P.signedHullLogVolume ∧
        P.ambient.logVolume P.ambient.hull < ⊤ := by
  obtain ⟨F, hF⟩ := s2457_Q_C_le_signedHull_of_paperCoverageRequired h
  exact ⟨F, hF, P.ambient_hull_logVolume_lt_top⟩

end PaperCoverage

/-! ## Status

* Exact/signed coverage is constructed from explicit actual-output witness
  structures, with no paper-family assumption.  Exact coverage is equivalent to
  the exact-witness structure; exact coverage and one-sided witnesses give the
  S1447 signed coverage; a single epsilon witness gives only Q_C <= H + eps.
* The pure-logic consumer s2457_Q_C_le_of_upper_coverage is S2452's
  s2452_Q_C_le_of_upper_coverage (the S1447 witness/midpoint argument).  The
  paper-family consumers use the S2452 family's upper and coverage fields and
  give Q_C <= -|log Theta|.
* s2457FixedCDataOfPaperFamily builds the S2362 fixed-C scalar with the
  xi_f_inequality field proved from the paper family, not assumed.  Exact
  paper coverage builds the S2362 C1 projection and readout on the actual
  Theorem 3.11 output carrier, and S2362's mainline scalar applies.
* S2457PaperCoverageRequired has no inhabitant in this file and none is
  constructed: this is the exact missing paper-family coverage.  The record is
  definitionally the S2452 paper-family requirement, whose coverage field is
  the exact/signed coverage.
* No fake object, no axiom and no sorry are used.  The C9 singleton
  bridgePossibleOutputs, the S1447 value-layer q-mark/readout and arbitrary
  output types are not used as the paper family.
* Checked by a direct lean invocation (no lake command) on 2026-11-03 with the
  project LEAN_PATH: EXIT=0, so statement compilation and proof checking
  succeeded.  The #print axioms lines report only propext, Classical.choice and
  Quot.sound for the probed declarations.
-/

#check S2457ExactOutputWitness
#check S2457OneSidedOutputWitness
#check S2457ApproxOutputWitness
#check s2457_exactCoverage_iff_witness
#check s2457_exactCoverage_of_witness
#check s2457_coverage_of_witness
#check s2457_signedCoverage_of_exactCoverage
#check s2457_signedCoverage_of_oneSidedWitness
#check s2457_Q_C_le_of_upper_exact
#check s2457_Q_C_le_of_upper_signed
#check s2457_Q_C_le_of_upper_coverage
#check s2457_Q_C_le_of_upper_witness
#check s2457_Q_C_le_of_upper_oneSidedWitness
#check s2457_Q_C_le_add_eps_of_approxWitness
#check s2457_paper_Q_C_le_of_upper_coverage
#check s2457_paper_Q_C_le_of_upper_exact
#check s2457_paper_Q_C_le_of_upper_signed
#check s2457_paper_Q_C_le_of_upper_witness
#check s2457_paper_Q_C_le_signedHull
#check s2457_paper_Q_C_le_signedHull_of_exact
#check s2457_paper_Q_C_le_signedHull_of_signed
#check s2457_paper_readout_eq_profile
#check s2457_paper_profile_le_signedHull
#check s2457_paper_to_S1447
#check s2457_paper_coverage_of_witness
#check s2457FixedCDataOfPaperFamily
#check s2457FixedCData_qPilotLogVolume
#check s2457_fixedC_scalar_of_paperFamily
#check s2457_fixedC_mainline_of_paperFamily
#check s2457_fixedC_qPilot_le_signedHull
#check s2457_fixedC_readout_eq_paper
#check s2457_fixedC_readout_le_signedHull
#check s2457S2362ProjectionOfExactPaperFamily
#check s2457S2362ReadoutOfExactPaperFamily
#check s2457S2362Readout_Q_C_eq_paper
#check s2457S2362Readout_le_signedHull
#check s2457S2362_mainline_of_exactPaperFamily
#check S2457PaperCoverageRequired
#check s2457_paperCoverageRequired_iff_s2452Required
#check s2457_paperCoverageRequired_iff_exists_family_coverage
#check s2457_Q_C_le_signedHull_of_paperCoverageRequired
#check s2457_mainline_of_paperCoverageRequired

#print axioms s2457_Q_C_le_of_upper_coverage
#print axioms s2457_paper_Q_C_le_signedHull
#print axioms s2457FixedCDataOfPaperFamily
#print axioms s2457_Q_C_le_signedHull_of_paperCoverageRequired

end LeanFormal.IUT.XiFPaper.S2457CoverageReadoutActual

end