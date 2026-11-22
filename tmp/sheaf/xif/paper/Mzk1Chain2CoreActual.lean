/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DifferentDictionaryActual
import Mathlib.Tactic

/-! # A881: chain 2 core — MODEL-level container (honest; not IUT objects) -/

/- MODEL (explicitly labelled, not paper objects):
* `Chain2Data`: base shell volume `baseShellVolume` (= paper logMuPaper model),
  `logp` (= log p at the fixed bad place), allowed ord interval `[allowedLower, allowedUpper]`
  (determined by the global constraint G), and the q-pilot order `qPilotOrd` with its
  membership in the interval (the Step-(xii) constraint keeps it);
* `shellVolume D := baseShellVolume - allowedLower * logp` (additive Haar scaling model:
  union over the interval is the largest shell, attained at the smallest order);
* requirement `req := (sFactor-1)*A` with `A = logQ/(2l)` (A779/A850 form);
* the IUT IV upper box is an explicit parameter `U`.

Proved: (a) q-pilot region membership (data field + monotone inclusion), (b) the model
implies the requirement and the upper box when the explicit interval inequalities hold,
(c) `G` not too strong = q-pilot stays inside the allowed interval, (d) a middle-case
existence theorem for the model with an explicit numerical witness.  All constants are
explicit; the global-constraint integer range is a PARAMETER (`allowedLower/Upper`), not
determined here. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Chain2CoreActual

structure Chain2Data where
  baseShellVolume : ℝ
  logp : ℝ
  logp_pos : 0 < logp
  allowedLower : ℝ
  allowedUpper : ℝ
  lower_le_upper : allowedLower ≤ allowedUpper
  qPilotOrd : ℝ
  qPilot_lower : allowedLower ≤ qPilotOrd
  qPilot_upper : qPilotOrd ≤ allowedUpper

def shellVolume (D : Chain2Data) : ℝ := D.baseShellVolume - D.allowedLower * D.logp

/-- (c) `G` not too strong: the q-pilot order stays in the allowed interval. -/
def qPilotInFamily (D : Chain2Data) : Prop :=
  D.allowedLower ≤ D.qPilotOrd ∧ D.qPilotOrd ≤ D.allowedUpper

theorem qPilotInFamily_holds (D : Chain2Data) : qPilotInFamily D :=
  ⟨D.qPilot_lower, D.qPilot_upper⟩

/-- (a) q-pilot region is contained in the possible image: in the model the possible image
is the shell at the smallest allowed order, and q-pilot's shell is among the family; the
containment reduces to the requirement `qPilotOrd >= allowedLower` (data field). -/
theorem qPilotRegion_subset_possibleImage (D : Chain2Data) :
    D.allowedLower ≤ D.qPilotOrd := D.qPilot_lower

/-- (b) **model implication**: explicit requirement/upper-box inequalities give the model
SSIneq-shape `req <= shellVolume D <= U`. -/
def ModelRequirementAndBox (D : Chain2Data) (req U : ℝ) : Prop :=
  req ≤ shellVolume D ∧ shellVolume D ≤ U

theorem model_requirement_and_box (D : Chain2Data) {req U : ℝ}
    (hreq : req ≤ shellVolume D) (hbox : shellVolume D ≤ U) :
    ModelRequirementAndBox D req U := ⟨hreq, hbox⟩

/-- (d) middle case: an explicit numerical witness of the model where the requirement and
the upper box both hold (numbers illustrative, not paper constants). -/
def middleWitnessData : Chain2Data where
  baseShellVolume := 3
  logp := 2
  logp_pos := by norm_num
  allowedLower := 0
  allowedUpper := 5
  lower_le_upper := by norm_num
  qPilotOrd := 0
  qPilot_lower := le_rfl
  qPilot_upper := by norm_num

theorem middle_case_exists : ModelRequirementAndBox middleWitnessData 2.5 4 := by
  unfold ModelRequirementAndBox shellVolume middleWitnessData
  constructor <;> norm_num

/-- Conditional chain-2 SSIneq-shape: if the actual Step-(xii) interval makes the model
volume lie between the requirement and the IUT IV box, then the model-level SSIneq shape
holds. -/
theorem chain2_model_ssIneq (D : Chain2Data) {req U : ℝ}
    (hmid : ModelRequirementAndBox D req U) : req ≤ shellVolume D := hmid.1

/-- **General survival condition**: `req <= base - allowedLower*logp` iff
`allowedLower <= (base - req)/logp` (for `logp > 0`). -/
theorem survival_iff (D : Chain2Data) {req : ℝ} :
    req ≤ shellVolume D ↔ D.allowedLower ≤ (D.baseShellVolume - req) / D.logp := by
  unfold shellVolume
  rw [le_div_iff₀ D.logp_pos]
  constructor <;> intro h <;> nlinarith

/-- Stage-4 corrected witness: `base = 0` and `allowedLower = -1` (t = -1 case). -/
def middleWitnessDataBaseZero : Chain2Data where
  baseShellVolume := 0
  logp := 2
  logp_pos := by norm_num
  allowedLower := -1
  allowedUpper := 0
  lower_le_upper := by norm_num
  qPilotOrd := -1
  qPilot_lower := le_rfl
  qPilot_upper := by norm_num

theorem middle_case_exists_baseZero :
    ModelRequirementAndBox middleWitnessDataBaseZero 1 3 := by
  unfold ModelRequirementAndBox shellVolume middleWitnessDataBaseZero
  constructor <;> norm_num
/-! ### A884: two-tier GlobalConstraint (G1 / G3), model-level -/

/- lana candidates (to be wired once `Iut/Wall*` oleans exist):
* G1: `Iut/LogLink/Thm311Rest.lean:473 rlf_unique` (`B.PF = B'.PF -> Nonempty (Unique (B.Iso B'))`)
  plus `Iut/ThetaLink/Link.lean:206 scaling_iff` (globally only the 1/s scaling); G1 forces the
  possible-image union to collapse to a single region;
* G2: `Iut/Concrete/Ind1Invariance.lean:144/192` (componentVol structural invariance);
* G3: `Iut/Concrete/LocalConstruct/ScaleVolume.lean:118` and `Prop14.lean:108`
  (exact componentVol scaling law) -- used when PF are inequivalent, via an ord-sum inequality.
Below they are abstract Prop fields/predicates; the model theorems are proved. -/

/-- G1-type constraint: the allowed ord interval collapses to a single point (PF equality
=> unique isomorphism => the union is one region). -/
def G1Type (D : Chain2Data) : Prop := D.allowedLower = D.allowedUpper

/-- G3-type constraint: the allowed interval width is bounded by an ord-sum budget. -/
def G3Type (D : Chain2Data) (budget : ℝ) : Prop := D.allowedUpper - D.allowedLower ≤ budget

/-- **G1 collapse (model)**: under a G1-type constraint the union volume is the single
region's volume. -/
theorem g1_union_eq_single (D : Chain2Data) (h : G1Type D) :
    shellVolume D = D.baseShellVolume - D.allowedLower * D.logp := rfl

/-- **G1 determines `allowedLower`**: the interval endpoints agree, so the lower bound is
the unique ord value. -/
theorem g1_allowedLower_unique (D : Chain2Data) (h : G1Type D) :
    D.allowedLower = D.allowedUpper := h

/-- **G1 survival is computable** from the PF data: same formula as `survival_iff`. -/
theorem g1_survival_computable (D : Chain2Data) (h : G1Type D) {req : ℝ} :
    req ≤ shellVolume D ↔ D.allowedLower ≤ (D.baseShellVolume - req) / D.logp := by
  exact survival_iff D

/-- **G3 survival criterion**: an ord-sum budget bounds the interval width; combined with
the lower endpoint criterion the volume window is controlled. -/
theorem g3_width_bound (D : Chain2Data) (budget : ℝ) (h : G3Type D budget) :
    D.allowedUpper - D.allowedLower ≤ budget := h

structure GlobalConstraintModel where
  g1 : Prop
  g3 : Prop

def chain2ConstraintRows : List (String × String × String) :=
  [ ("G1 rlf_unique", "Iut/LogLink/Thm311Rest.lean:473", "LANA (olean needed)") ,
    ("G1 scaling_iff", "Iut/ThetaLink/Link.lean:206", "LANA (olean needed)") ,
    ("G2 Ind1Invariance", "Iut/Concrete/Ind1Invariance.lean:144/192", "LANA (olean needed)") ,
    ("G3 ScaleVolume/Prop14", "Iut/Concrete/LocalConstruct/ScaleVolume.lean:118; Prop14.lean:108", "LANA (olean needed)") ,
    ("G1Type", "allowedLower = allowedUpper (collapse)", "MODEL DEF") ,
    ("G3Type", "allowedUpper - allowedLower <= budget", "MODEL DEF") ,
    ("g1_union_eq_single", "G1 => single-region volume", "PROVED (model)") ,
    ("g1_survival_computable", "G1 => survival by PF data", "PROVED (model)") ]

theorem chain2ConstraintRows_length : chain2ConstraintRows.length = 8 := rfl
/-! ### A892: does the base include the archimedean term?  DECISION: YES -/

/- Evidence:
* ROUTES 12.1 L5 (`coord/ROUTES-FINAL-GAP.md:357`): `V = ((l+5)/4)*D_exact`,
  `D_exact := sum_w weight_w*h_w*log p_w + INFINITE-PLACE TERMS`; L362 collects the
  infinite-place contribution as a FIXED `C0` but does not remove it;
* lana `logVol_hull_vcI_eq` sums `hullPacket` over ALL rational places including `vQ = infty`
  (arch component via `archDefect`/`archLogShell`); `hullPacket_finite`/`hullPacket_tame`
  are only the finite-place terms (`Mzk1HullPacketFormulaActual:806/844`);
* `Mzk1DifferentDictionaryActual`: `diffPaperPerPlace = -order*logp - r/n + arch` with
  `archConstant = log(sqrt 2 * pi)` -- arch is part of the paper dictionary, not discarded.
So the chain-2 base must be `finiteTerm + arch - torsion`.  For p=11 (e=n=1, r=0),
`logMuPaper = 0` and base = `archConstant` (≈1.4913), so a G1-type constraint with t=0
gives V=1.4913 inside the window [0.4637, 5.9947]: **G1 alive under the arch-included base**.
(Under the finite-only base=0 hypothesis the G1 case would die and only G3 survives.) -/

open LeanFormal.IUT.XiFPaper.Mzk1DifferentDictionaryActual

def chain2BaseWithArch (finiteTerm arch torsion : ℝ) : ℝ := finiteTerm + arch - torsion

def chain2BaseFiniteOnly (finiteTerm : ℝ) : ℝ := finiteTerm

def archBaseData : Chain2Data where
  baseShellVolume := archConstant
  logp := Real.log 11
  logp_pos := Real.log_pos (by norm_num)
  allowedLower := 0
  allowedUpper := 5
  lower_le_upper := by norm_num
  qPilotOrd := 0
  qPilot_lower := le_rfl
  qPilot_upper := by norm_num

theorem middle_case_arch_within (hlo : (0.46365 : ℝ) ≤ archConstant)
    (hhi : archConstant ≤ 5.9947) :
    ModelRequirementAndBox archBaseData 0.46365 5.9947 := by
  unfold ModelRequirementAndBox shellVolume archBaseData
  constructor
  · simpa using hlo
  · simpa using hhi
/-! ### A893: multi-bad-place model -- archimedean term appears GLOBALLY once -/

/- The archimedean contribution comes from the infinite place(s), not from each finite bad
place: `base(k) = sum_i finiteTerm_i + arch_global - sum_i torsion_i`, with `arch_global`
counted once (per archimedean factor, per paper). -/

def chain2BaseMulti {k : ℕ} (finiteTerm torsion : Fin k → ℝ) (archGlobal : ℝ) : ℝ :=
  (∑ i, finiteTerm i) + archGlobal - (∑ i, torsion i)

theorem chain2BaseMulti_single (finite arch torsion : ℝ) :
    chain2BaseMulti (k := 1) (fun _ => finite) (fun _ => torsion) arch =
      finite + arch - torsion := by
  unfold chain2BaseMulti
  simp

/-- p=11 and p=2 model: finite terms 0 and (3/4)log 2, torsion 0, arch once. -/
def p11p2Base : ℝ :=
  chain2BaseMulti (k := 2)
    (fun i => if (i : ℕ) = 0 then 0 else (3 / 4) * Real.log 2)
    (fun _ => 0) archConstant

theorem p11p2Base_eq (h : (3 / 4) * Real.log 2 = (3 / 4) * Real.log 2) :
    p11p2Base = (3 / 4) * Real.log 2 + archConstant := by
  unfold p11p2Base chain2BaseMulti
  simp

/-- G1-type (t=0) survives in the multi-place model whenever the global base lies in the
window [req, U] (hypotheses explicit). -/
theorem g1_multi_survives_in_window {V req U : ℝ} (hlo : req ≤ V) (hhi : V ≤ U) :
    req ≤ V ∧ V ≤ U := ⟨hlo, hhi⟩
/-! ### A896: collapse lemma -- chain 2 is equivalent to req <= U -/

/-- **Collapse lemma**: `exists t, req <= base - t*logp <= U` is equivalent to `req <= U`.
The constraint/interval parameters disappear. -/
theorem collapse_iff (base logp req U : ℝ) (hlogp : logp ≠ 0) :
    (∃ t : ℝ, req ≤ base - t * logp ∧ base - t * logp ≤ U) ↔ req ≤ U := by
  constructor
  · rintro ⟨t, h1, h2⟩
    linarith
  · intro h
    refine ⟨(base - req) / logp, ?_, ?_⟩
    · have ht : base - ((base - req) / logp) * logp = req := by
        field_simp [hlogp]
        ring
      rw [ht]
    · have ht : base - ((base - req) / logp) * logp = req := by
        field_simp [hlogp]
        ring
      rw [ht]
      exact h

/-- Unconditional form: any shell containing the q-pilot (`req <= VolShell`) whose volume is
bounded by `U` yields `req <= U`. -/
theorem req_le_U_of_vol_bounds {req U V : ℝ} (h1 : req ≤ V) (h2 : V ≤ U) : req ≤ U :=
  le_trans h1 h2

def chain2CoreRows : List (String × String × String) :=
  [ ("Chain2Data", "baseShellVolume/logp/[allowedLower,upper]/qPilotOrd", "MODEL DEF (qPilotOrd NOT in volume formula)") ,
    ("shellVolume", "base - allowedLower*logp (union = max shell)", "MODEL DEF") ,
    ("qPilotInFamily", "lower <= qPilotOrd <= upper", "DATA FIELD (downgraded)") ,
    ("qPilotRegion_subset_possibleImage", "= qPilot_lower field", "TAG: field, not theorem") ,
    ("ModelRequirementAndBox", "req <= V <= U", "DEF") ,
    ("chain2_model_ssIneq", "= hmid.1", "TAG: projection only") ,
    ("middle_case_exists", "numerical witness 2.5 <= 3 <= 4", "PROVED (trivial) ") ,
    ("middle_case_exists_baseZero", "base=0, allowedLower=-1 => 1 <= 2 <= 3", "PROVED") ,
    ("survival_iff", "req <= V <-> allowedLower <= (base-req)/logp", "PROVED") ,
    ("base includes arch", "finite + arch_global - torsion, arch ONCE", "DECISION + MODEL DEF") ,
    ("middle_case_arch_within", "arch base => t=0 in window (conditional)", "PROVED (conditional)") ,
    ("chain2BaseMulti", "sum finite + arch_global - sum torsion", "MODEL DEF (arch once)") ,
    ("p11p2Base", "p=11(0)+p=2((3/4)log2)+arch once", "MODEL DEF") ,
    ("g1_multi_survives_in_window", "G1 t=0 survives iff base in [req,U]", "PROVED (conditional)") ,
    ("collapse_iff", "exists t window <-> req <= U", "PROVED (A896) ") ,
    ("req_le_U_of_vol_bounds", "req<=V and V<=U => req<=U", "PROVED (A896) ") ,
    ("g1_union_eq_single", "= rfl (model)", "TAG: trivial") ,
    ("pf_eq_unique_iso / scalingUnique", "free Prop fields", "TAG: free props, unused in volume") ,
    ("registered conclusion", "chain 2 equivalent to req <= U, not independent", "REGISTERED") ,
    ("missing real theorem", "qPilotRegion subset P => (s-1)A <= VolShell P (dictionary)", "MISSING (lana objects)") ]

theorem chain2CoreRows_length : chain2CoreRows.length = 20 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Chain2CoreActual
