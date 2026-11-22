/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Chain2CoreActual
import Mathlib.Tactic

/-! # A887: chain 2 real-object statements C2.1 / C2.2 (interfaces; model-level bridges) -/

/- REAL OBJECT REFERENCES (fields; to be wired to lana once oleans exist):
* `ValBPS`/`PF`/`rlf` data of `Iut/LogLink/Thm311Rest.lean:473` (`rlf_unique`);
* global scaling `Iut/ThetaLink/Link.lean:206` (`scaling_iff`, only 1/s);
* `componentVol` scaling law `Iut/Concrete/LocalConstruct/ScaleVolume.lean:118`,
  `Prop14.lean:108` (`componentVol_prod_incl_smul_integral`);
* G2 invariance `Iut/Concrete/Ind1Invariance.lean:144/192`.

C2.1: the q-pilot (1,0) implementation is a family member; formulated via PF equality
      and the unique-isomorphism condition.
C2.2: G1-type (PF equal => single region) and G3-type (ord-sum budget) each bound the
      shell volume by the IUT IV upper box.

Model-level bridges proved below; the real objects are interface fields. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Chain2RealActual

open LeanFormal.IUT.XiFPaper.Mzk1Chain2CoreActual

structure Chain2RealObjects where
  valBPS : Type
  PF : valBPS → Type
  rlfIso : valBPS → valBPS → Type
  pf_eq_unique_iso : Prop
  scalingUnique : Prop
  componentVolScale : valBPS → ℝ

/-- **C2.1**: q-pilot (1,0) is in the family (PF equality + unique iso + interval member). -/
def C21Statement (R : Chain2RealObjects) (D : Chain2Data) : Prop :=
  R.pf_eq_unique_iso ∧ R.scalingUnique ∧ D.allowedLower ≤ D.qPilotOrd

theorem c21_of_data (R : Chain2RealObjects) (D : Chain2Data)
    (hpf : R.pf_eq_unique_iso) (hsc : R.scalingUnique) :
    C21Statement R D := ⟨hpf, hsc, D.qPilot_lower⟩

/-- **C2.2 (G1-type)**: PF equality => single region => shell volume bounded by U. -/
def C22StatementG1 (R : Chain2RealObjects) (D : Chain2Data) (U : ℝ) : Prop :=
  G1Type D ∧ shellVolume D ≤ U

theorem c22_g1_of_bounds (R : Chain2RealObjects) (D : Chain2Data) {U : ℝ}
    (h1 : G1Type D) (hU : shellVolume D ≤ U) : C22StatementG1 R D U := ⟨h1, hU⟩

/-- **C2.2 (G3-type)**: ord-sum budget + requirement + upper box. -/
def C22StatementG3 (R : Chain2RealObjects) (D : Chain2Data)
    (budget req U : ℝ) : Prop :=
  G3Type D budget ∧ req ≤ shellVolume D ∧ shellVolume D ≤ U

theorem c22_g3_of_bounds (R : Chain2RealObjects) (D : Chain2Data) {budget req U : ℝ}
    (h3 : G3Type D budget) (hmid : ModelRequirementAndBox D req U) :
    C22StatementG3 R D budget req U := ⟨h3, hmid.1, hmid.2⟩

/-- G1 specialization: `g1_union_eq_single` transported to C2.2. -/
theorem c22_g1_model (R : Chain2RealObjects) (D : Chain2Data) {U : ℝ}
    (h1 : G1Type D) (hU : D.baseShellVolume - D.allowedLower * D.logp ≤ U) :
    C22StatementG1 R D U := ⟨h1, hU⟩

def chain2RealRows : List (String × String × String) :=
  [ ("C2.1", "PF equality + unique iso + qPilot interval member", "STATEMENT (interface)") ,
    ("c21_of_data", "PF/scaling props + data field => C2.1", "PROVED (model)") ,
    ("C2.2 G1", "single region = G1 => volume <= U", "STATEMENT + PROVED bridge") ,
    ("C2.2 G3", "ord-sum budget => req <= V <= U", "STATEMENT + PROVED bridge") ,
    ("PF equality realization", "ValBPS/PF/rlf objects of lana", "REMAINING PARAM (olean)") ,
    ("scaling 1/s identification", "scaling_iff", "REMAINING PARAM (olean)") ,
    ("componentVol ord sum", "ScaleVolume/Prop14", "REMAINING PARAM (olean)") ,
    ("componentVol_prod_incl_smul_integral statement", "lana exact signature", "NOT READ (olean)") ]

theorem chain2RealRows_length : chain2RealRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Chain2RealActual
