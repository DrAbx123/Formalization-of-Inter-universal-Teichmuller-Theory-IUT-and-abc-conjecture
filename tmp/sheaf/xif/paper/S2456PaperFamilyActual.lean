import tmp.sheaf.xif.paper.S2452XiFCoverageActual

/-!
# S2456: actual paper output family P_C, nu_C, Q_C

This file attempts to construct the paper fixed-C output family of
S2452PaperOutputFamily from the objects available in the tree, without
using the C9 singleton bridge or the value-layer q-mark as a substitute.
The attempt stops at the exact missing source object: there is no actual
paper final-evaluation family P_C, no paper readout nu_C, no paper
q-normalization Q_C = -|log q| identified with a source scalar, and no
exact/signed coverage statement for such a family.

What is recorded here:

* S2456ActualPaperFamilyRequired is the exact missing subinterface:
  the actual restricted paper family P_C, the paper q and its readout
  nu_C, the q-pilot scalar Q_C with Q_C = -|log q|, the pointwise
  profile-readout equality, the paper hull upper bound, and exact-or-signed
  coverage.
* S2456ActualPaperFamilyRequired.toS2452 proves that any inhabitant of
  this subinterface yields S2452PaperOutputFamily.
* S2456ActualPaperFamilyRequired.ofS2452 is the converse forgetful map, so the
  recorded subinterface is exactly equivalent to the S2452 family (up to
  deriving nonemptiness of P_C from coverage).
* s2456ActualPaperFamilyRequired_iff_S2452 records the equivalence of
  the two existence statements.

No inhabitant of S2456ActualPaperFamilyRequired is constructed, and no
sorry, custom axiom, True, PUnit, empty type, singleton bridge family, or
value-layer q-mark family is used.  The source gap is recorded, not closed
by fabrication. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2456PaperFamilyActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.C9IUTBridgeOutput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1447MarkedTraceActual
open LeanFormal.IUT.XiFPaper.S2452XiFCoverageActual
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge

universe u v w ux

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice] [Fintype Label]
  {X : Type ux} {P : PaperSignedHull X Label}
  {R : SourceTheorem311Realization l Label Choice}

/-! ## 1. The exact missing paper-family subinterface -/

/-- The exact missing actual paper output family of Corollary 3.12.

The fields are the paper objects, not project substitutes:

* P_C is the restricted paper final-evaluation output family in the
  actual output carrier ActualOutput R; it is not the C9 singleton
  bridgePossibleOutputs b.out and not the value-layer theta-pilot image
  set.
* q is the paper q parameter, with 0 < q and q != 1.
* nu_C is the paper output readout, not the S1447 value-layer readout.
* Q_C is the paper q-pilot scalar with Q_C = -|log q|.
* readout_eq is the pointwise identification of nu_C with the actual
  source profile log-volume.
* upper is the paper hull upper bound by P.signedHullLogVolume.
* coverage is the exact-or-signed output-readout coverage of Q_C.

No term of this structure is constructed here. -/
structure S2456ActualPaperFamilyRequired
    (P : PaperSignedHull X Label)
    (R : SourceTheorem311Realization l Label Choice) where
  /-- The actual restricted paper final-evaluation family. -/
  P_C : Set (ActualOutput R)
  /-- The paper q parameter. -/
  q : Real
  /-- The paper q parameter is positive. -/
  q_pos : 0 < q
  /-- The paper q parameter is not one. -/
  q_ne_one : q ≠ 1
  /-- The actual paper output readout. -/
  nu_C : ActualOutput R → Real
  /-- The paper q-pilot scalar. -/
  Q_C : Real
  /-- The paper q-pilot normalization Q_C = -|log q|. -/
  Q_C_eq_neg_abs_log_q : Q_C = -( |Real.log q| )
  /-- The readout is the actual source profile log-volume. -/
  readout_eq : ∀ D, D ∈ P_C → nu_C D =
    R.input.profile.logVolume D.source
  /-- The paper hull upper bound. -/
  upper : ∀ D, D ∈ P_C → nu_C D ≤ P.signedHullLogVolume
  /-- Exact or signed output-readout coverage of the paper q scalar. -/
  coverage : S2452Coverage P_C nu_C Q_C

namespace S2456ActualPaperFamilyRequired

variable (F : S2456ActualPaperFamilyRequired P R)

/-- The paper family is nonempty.  This is not an extra field: exact
coverage exhibits a member, and signed coverage exhibits one at any
positive epsilon. -/
theorem P_C_nonempty : F.P_C.Nonempty := by
  have h : S1447ExactCoverage F.P_C F.nu_C F.Q_C ∨
      S1447SignedCoverage F.P_C F.nu_C F.Q_C := F.coverage
  rcases h with ⟨D, hD, _⟩ | hcov
  · exact ⟨D, hD⟩
  · obtain ⟨D, hD, _⟩ := hcov 1 (by norm_num)
    exact ⟨D, hD⟩

/-- Any inhabitant of the exact missing subinterface yields the S2452 paper
output family.  This is a forgetful map: P_C, nu_C, Q_C, the readout
equation, the upper bound, and the coverage are preserved definitionally. -/
def toS2452 : S2452PaperOutputFamily P R where
  P_C := F.P_C
  P_C_nonempty := F.P_C_nonempty
  q := F.q
  q_pos := F.q_pos
  q_ne_one := F.q_ne_one
  nu_C := F.nu_C
  Q_C := F.Q_C
  Q_C_eq_neg_abs_log_q := F.Q_C_eq_neg_abs_log_q
  readout_eq := F.readout_eq
  upper := F.upper
  coverage := F.coverage

@[simp] theorem toS2452_P_C : F.toS2452.P_C = F.P_C := rfl

@[simp] theorem toS2452_nu_C : F.toS2452.nu_C = F.nu_C := rfl

@[simp] theorem toS2452_Q_C : F.toS2452.Q_C = F.Q_C := rfl

/-- The profile-readout identification, restated. -/
theorem readout_eq_profile (D : ActualOutput R) (hD : D ∈ F.P_C) :
    F.nu_C D = R.input.profile.logVolume D.source :=
  F.readout_eq D hD

/-- Every paper-family output readout is under the signed paper hull. -/
theorem profile_le_signedHull (D : ActualOutput R) (hD : D ∈ F.P_C) :
    R.input.profile.logVolume D.source ≤ P.signedHullLogVolume := by
  rw [← F.readout_eq D hD]
  exact F.upper D hD

/-- The exact-or-signed coverage field, exposed as the S1447 projection. -/
theorem to_S1447_projection :
    S1447OutputReadoutProjection F.P_C F.nu_C F.Q_C :=
  F.coverage

/-- The S1447 scalar consumer, specialized to the actual paper family. -/
theorem Q_C_le_signedHull : F.Q_C ≤ P.signedHullLogVolume :=
  F.toS2452.Q_C_le_signedHull

end S2456ActualPaperFamilyRequired

/-! ## 2. Converse map and exact equivalence with S2452 -/

/-- Any S2452 paper output family forgets to the exact missing subinterface.
This proves the recorded subinterface is not stronger than S2452: no extra
paper data is required beyond the S2452 fields. -/
def S2456ActualPaperFamilyRequired.ofS2452 (F : S2452PaperOutputFamily P R) :
    S2456ActualPaperFamilyRequired P R where
  P_C := F.P_C
  q := F.q
  q_pos := F.q_pos
  q_ne_one := F.q_ne_one
  nu_C := F.nu_C
  Q_C := F.Q_C
  Q_C_eq_neg_abs_log_q := F.Q_C_eq_neg_abs_log_q
  readout_eq := F.readout_eq
  upper := F.upper
  coverage := F.coverage

/-- Any inhabitant of the exact missing subinterface yields the S2452 paper
output family existence statement.  The term-level construction is
`S2456ActualPaperFamilyRequired.toS2452`. -/
theorem s2456_actualPaperFamilyRequired_yields_S2452
    (F : S2456ActualPaperFamilyRequired P R) :
    S2452PaperOutputFamilyRequired P R :=
  ⟨F.toS2452⟩

/-- Nonempty form of the same implication. -/
theorem s2456ActualPaperFamilyRequired_yields_S2452Required
    (h : Nonempty (S2456ActualPaperFamilyRequired P R)) :
    S2452PaperOutputFamilyRequired P R :=
  h.elim fun F => ⟨F.toS2452⟩

/-- Conversely, an S2452 paper output family yields the recorded exact
missing subinterface. -/
theorem s2452Required_yields_s2456ActualPaperFamilyRequired
    (h : S2452PaperOutputFamilyRequired P R) :
    Nonempty (S2456ActualPaperFamilyRequired P R) :=
  h.elim fun F => ⟨S2456ActualPaperFamilyRequired.ofS2452 F⟩

/-- The recorded exact missing subinterface and the S2452 paper output family
are equivalent existence statements.  This is an equivalence of interfaces,
not a construction of either one. -/
theorem s2456ActualPaperFamilyRequired_iff_S2452 :
    Nonempty (S2456ActualPaperFamilyRequired P R) ↔
      S2452PaperOutputFamilyRequired P R :=
  ⟨s2456ActualPaperFamilyRequired_yields_S2452Required,
    s2452Required_yields_s2456ActualPaperFamilyRequired⟩

/-! ## 3. Why the available objects do not give an inhabitant

The direct routes were checked before recording the interface:

* theorem311Output R.input inhabits ActualOutput R, but choosing
  P_C = {theorem311Output R.input} is exactly the forbidden singleton
  fake; the paper P_C is a restricted final-evaluation family, not a
  one-point set.
* The C9 bridge set bridgePossibleOutputs b.out is a singleton by
  BridgeOutput.possibleOutputs_eq_singleton.  Using it as P_C would
  require the missing profile-readout/q identification (recorded in S2373
  and S2396) and the paper hull upper bound; the bridge has neither field.
* The S1447 value-layer allowedOutputSource is a set of
  I.ThetaPilotPoint v, not of ActualOutput R, and its readout is the
  source local log-degree, not R.input.profile.logVolume.  It therefore
  cannot fill P_C or nu_C in this interface.
* The S1447 qMark value is a value-layer source scalar, not the paper
  Q_C = -|log q|; no identification of the two is present in the tree.

The first unavailable item is the actual paper family P_C itself; the
readout equation, upper bound, and coverage are then missing fields of that
same source object.  This file therefore records them and proves only the
conditional passage to S2452. -/

/-! ## Status

* S2456ActualPaperFamilyRequired is an interface with no inhabitant.
* S2456ActualPaperFamilyRequired.toS2452 constructs
  S2452PaperOutputFamily from any inhabitant.
* The converse map and the equivalence of existence statements are proved.
* No singleton, value-layer readout, True, PUnit, empty type, sorry,
  or custom axiom is used.  The key declarations depend only on the allowed
  propext, Classical.choice, and Quot.sound (checked with #print axioms).
* This file was not built with lake.  It was checked by direct lean
  invocation against the existing S2452 olean (no lake command). -/

#check S2456ActualPaperFamilyRequired
#check S2456ActualPaperFamilyRequired.P_C
#check S2456ActualPaperFamilyRequired.nu_C
#check S2456ActualPaperFamilyRequired.Q_C
#check S2456ActualPaperFamilyRequired.readout_eq
#check S2456ActualPaperFamilyRequired.upper
#check S2456ActualPaperFamilyRequired.coverage
#check S2456ActualPaperFamilyRequired.P_C_nonempty
#check S2456ActualPaperFamilyRequired.toS2452
#check S2456ActualPaperFamilyRequired.Q_C_le_signedHull
#check S2456ActualPaperFamilyRequired.ofS2452
#check s2456_actualPaperFamilyRequired_yields_S2452
#check s2456ActualPaperFamilyRequired_yields_S2452Required
#check s2452Required_yields_s2456ActualPaperFamilyRequired
#check s2456ActualPaperFamilyRequired_iff_S2452

end LeanFormal.IUT.XiFPaper.S2456PaperFamilyActual

end
