import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealEdgeNormalizationDichotomy

/-!
# R9 form audit: point membership, witness, and value forms (report T1)

Task `hunit-epsilon-transfer-20261016`.  Audit of the comparison form of the
Corollary 3.12 Step (xi) engine against the original.

Corpus anchors (IUT III): the down-ray
`R_<=(-|log(Theta)|) = {lambda in R | lambda <= -|log(Theta)|}` (lines
10843-10845); the point membership `-|log(q)| in R_<=(-|log(Theta)|)` (line
10895) read off as the inequality `-|log(q)| <= -|log(Theta)|` (lines
10895-10896); the realness/bookkeeping statements `-|log(Theta)| in R`,
`-|log(q)| in R`, `C_Theta >= -1` (lines 10326, 10340, 10351-10353).

Proved here:
* ray membership is the endpoint inequality (`mem_downRay_iff_le`): the paper's
  "hence also" step is exactly this unfolding of the down-ray;
* membership in the down-closure of a family is a single-point witness, i.e. a
  dominating member (`mem_iUnion_downRay_iff_exists_le`);
* a family-supremum comparison against a constant is the pointwise comparison
  (`csSup_image_le_iff_forall_le`), and it is equivalent to the witness form
  exactly when a dominating element exists
  (`witness_iff_le_csSup_of_isGreatest`);
* the value/supremum form is strictly weaker than the witness form in general
  (`valueForm_not_witnessForm_calibration`,
  `valueForm_strictly_weaker_than_witnessForm`).

Lift to the repository R9 objects: R9 holds exactly when every point of the
holomorphic hull has point log-volume in the down-ray of the edge volume
(`sourceHullVolume_le_iff_pointwise_pointVolume_le`), equivalently when every
hull log-degree is at most the real edge value
(`sourceHullVolume_le_iff_points_logDegree_le_toReal`).

Honesty boundary: the dictionary and its lifting are unconditional; the
identification of the paper's `-|log(Theta)|` / `-|log(q)|` with specific
repository values on the true `1,circ U` carrier remains open (Card-HULLREAL)
and is not asserted.  The repository R9 inequality is a sup-form; by the
calibration it is not strictly stronger than the paper's membership form: the
two coincide when the edge supremum is attained and the sup-form alone
otherwise fails to produce the dominating member.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
universe u v ua uv upi umon ui


/-! ## 1. Membership, witness, and value forms on the real line -/

/-- The down-ray `R_<=c = {lambda | lambda <= c}` of the Step (xi) engine
(III:10845). -/
def downRay (c : Real) : Set Real := Set.Iic c

/-- **Ray membership is the endpoint inequality**: the paper's step "the
inclusion ..., hence also the inequality" (III:10895-10896) is exactly the
unfolding of the down-ray. -/
theorem mem_downRay_iff_le (x c : Real) : x ∈ downRay c ↔ x ≤ c :=
  Set.mem_Iic

/-- Down-closure membership is a single-point witness: membership of `x` in the
union of the down-rays over a family is exactly the existence of a dominating
member. -/
theorem mem_iUnion_downRay_iff_exists_le (x : Real) (S : Set Real) :
    x ∈ (⋃ y ∈ S, downRay y) ↔ ∃ y ∈ S, x ≤ y := by
  unfold downRay
  simp only [Set.mem_iUnion, Set.mem_Iic, exists_prop]

/-- **Sup-form vs pointwise form.**  For a nonempty family with bounded-above
image, the comparison of the image supremum against a constant is exactly the
pointwise comparison of the members. -/
theorem csSup_image_le_iff_forall_le {S : Set Real} (f : Real → Real) {c : Real}
    (hne : S.Nonempty) (hbdd : BddAbove (f '' S)) :
    sSup (f '' S) ≤ c ↔ ∀ z ∈ S, f z ≤ c := by
  constructor
  · intro h z hz
    exact le_trans (le_csSup hbdd ⟨z, hz, rfl⟩) h
  · intro h
    obtain ⟨z, hz⟩ := hne
    exact csSup_le ⟨f z, z, hz, rfl⟩ (by rintro y ⟨z, hz, rfl⟩; exact h z hz)

/-- **Attained sup: value form iff witness form.**  When the family has a
greatest element (the dominating element), the value comparison and the
single-point witness comparison are equivalent. -/
theorem witness_iff_le_csSup_of_isGreatest {S : Set Real} {m : Real}
    (hm : IsGreatest S m) (x : Real) :
    (∃ y ∈ S, x ≤ y) ↔ x ≤ sSup S := by
  have hsup : sSup S = m :=
    le_antisymm (csSup_le ⟨m, hm.1⟩ fun b hb => hm.2 hb)
      (le_csSup ⟨m, hm.2⟩ hm.1)
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [hsup]
    exact hxy.trans (hm.2 hy)
  · intro h
    rw [hsup] at h
    exact ⟨m, hm.1, h⟩

/-- **Strictness calibration.**  The value/supremum form does not imply the
witness form when the supremum is not attained: `1 <= sSup (Iio 1)` holds, but
no member of `Iio 1` dominates `1`. -/
theorem valueForm_not_witnessForm_calibration :
    1 ≤ sSup (Set.Iio (1 : Real)) ∧ ¬ ∃ y ∈ Set.Iio (1 : Real), 1 ≤ y := by
  have hsup : sSup (Set.Iio (1 : Real)) = 1 := by
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨0, by norm_num⟩ ?_ ?_
    · rintro a ha
      exact le_of_lt ha
    · intro w hw
      refine ⟨(w + 1) / 2, ?_, ?_⟩
      · change (w + 1) / 2 < 1
        linarith
      · linarith
  constructor
  · rw [hsup]
  · rintro ⟨y, hy, hy_le⟩
    exact absurd hy_le (not_le.mpr hy)

/-- The value/supremum form is strictly weaker than the witness/dominating-
element form in general. -/
theorem valueForm_strictly_weaker_than_witnessForm :
    ∃ (S : Set Real) (x : Real), x ≤ sSup S ∧ ¬ ∃ y ∈ S, x ≤ y :=
  ⟨Set.Iio (1 : Real), 1, valueForm_not_witnessForm_calibration⟩

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 2. Lifting the dictionary to the R9 objects -/

/-- **Point-membership form of R9.**  R9 holds exactly when every point of the
holomorphic hull has point log-volume in the down-ray of the edge volume: the
family-valued analogue of the paper's point-membership engine
`-|log(q)| in R_<=(-|log(Theta)|)` (III:10895). -/
theorem sourceHullVolume_le_iff_pointwise_pointVolume_le (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n ↔
      ∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourcePointVolume v z ≤ I.sourceImageVolume v R n := by
  unfold sourceHullVolume sourceSetVolume
  constructor
  · intro h z hz
    exact le_trans (le_iSup₂_of_le z hz le_rfl) h
  · intro h
    exact iSup_le fun z => iSup_le fun hz => h z hz

/-- Point volume vs a real endpoint: the `ofReal`-form of ray membership. -/
theorem sourcePointVolume_le_ofReal_iff (v : V) (z : I.ThetaPilotPoint v)
    {c : Real} (hc : 0 ≤ c) :
    I.sourcePointVolume v z ≤ ENNReal.ofReal c ↔ I.sourceLocalLogDegree v z ≤ c := by
  unfold sourcePointVolume
  exact ENNReal.ofReal_le_ofReal_iff hc

/-- **Real-valued endpoint form of R9.**  R9 holds exactly when every hull
log-degree is at most the real edge value `(sourceImageVolume).toReal`: the
value-inequality form matching the paper's `-|log(q)| <= -|log(Theta)|`
(III:10896) at the value layer. -/
theorem sourceHullVolume_le_iff_points_logDegree_le_toReal (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n ↔
      ∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourceLocalLogDegree v z ≤ (I.sourceImageVolume v R n).toReal := by
  rw [sourceHullVolume_le_iff_pointwise_pointVolume_le I v R n]
  have hfin : I.sourceImageVolume v R n ≠ ⊤ :=
    ne_top_of_lt (sourceImageVolume_lt_top I v R n)
  constructor
  · intro h z hz
    have h1 : I.sourcePointVolume v z ≤
        ENNReal.ofReal (I.sourceImageVolume v R n).toReal := by
      rw [ENNReal.ofReal_toReal hfin]
      exact h z hz
    exact (sourcePointVolume_le_ofReal_iff I v z ENNReal.toReal_nonneg).mp h1
  · intro h z hz
    have h1 : I.sourcePointVolume v z ≤
        ENNReal.ofReal (I.sourceImageVolume v R n).toReal :=
      (sourcePointVolume_le_ofReal_iff I v z ENNReal.toReal_nonneg).mpr (h z hz)
    rwa [ENNReal.ofReal_toReal hfin] at h1

end OriginalInput
end Theorem311Source

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the T1 form audit of the R9 comparison form (report
section 21). -/
def cardHullRealR9PointMembershipAudit : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-r9-point-membership-audit"
    source :=
      "IUT III, Corollary 3.12, Step (xi): down-ray definition III:10843-10845; " ++
        "point membership and inequality reading III:10895-10896; realness and " ++
        "bookkeeping III:10326, 10340, 10351-10353"
    status := VerificationStatus.interface
    note :=
      "T1 form audit. Proved: ray membership iff endpoint inequality; " ++
        "down-closure membership iff single-point witness; sup comparison iff " ++
        "pointwise comparison (nonempty, bounded above); witness iff value form " ++
        "when a dominating element exists; strict separation calibration when " ++
        "the sup is unattained. Lifted to R9: hull <= image iff every hull " ++
        "point has point volume in the down-ray of the edge volume; iff every " ++
        "hull log-degree is at most the real edge value. NOT claimed: the " ++
        "identification of the paper's -|log(Theta)| / -|log(q)| with " ++
        "repository values on the true carrier (Card-HULLREAL open)."
    dependsOn :=
      [ "IUT-III.corollary-3.12-card-hullreal-edge-normalization-dichotomy",
        "IUT-III.corollary-3.12-card-hullreal-edge-normalization-reduction" ] }

end LeanFormal.IUT.Audit
