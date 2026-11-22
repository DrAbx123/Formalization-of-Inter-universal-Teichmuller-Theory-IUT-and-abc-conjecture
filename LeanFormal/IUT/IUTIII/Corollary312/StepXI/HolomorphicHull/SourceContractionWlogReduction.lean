import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceContractedSupplyRealization

/-!
  # Pushing down the contraction residuals: the paper's WLOG and the scaling obstruction

  `SourceContractedSupplyRealization.lean` closes the Card-HULLREAL supplies from two
  explicit hypotheses on the realized theta-pilot packet (the "contracted generators"):

  * `hImage`: nonpositive log-degree of every theta-pilot image point;
  * `hScaling`: nonpositive log-degree of every hull scaling.

  This module pushes both down as far as the value layer allows, with a mixed outcome
  that is recorded honestly.

  ## Route 1: the paper's WLOG is a sign case split (closed, mechanized)

  IUT III, corpus lines 10354-10358 (Corollary 3.12 proof, opening of Step (xi)):
  "since |log(q)| > 0, we may assume without loss of generality in the remainder of
  the proof that -|log(Theta)| < 0 whenever -|log(Theta)| in R [i.e., since an
  inequality -|log(Theta)| >= 0 would imply that -|log(Theta)| >= 0 > -|log(q)|]".

  The mechanism is not a conjugation or a positive-power transform: it is the
  elementary sign split of the target inequality `-|log(q)| <= -|log(Theta)|`.  If
  `-|log(Theta)| >= 0`, the inequality is immediate from `-|log(q)| < 0` (itself from
  `|log(q)| > 0`, i.e. `q > 0` and `q != 1`); hence one may assume the negative
  branch.  This is mechanized in section 1 (`neg_abs_log_le_of_wlog_negative_case`,
  with the trivial branch `neg_abs_log_le_of_nonneg_right`), together with the
  coefficient rider `C_Theta >= -1` of lines 10352-10353 / 10895-10898
  (`coefficient_ge_neg_one_of_neg_abs_log_le`), and instantiated at the actual source
  theta packet in section 2.  This reduction is a statement about the final
  inequality; it does not manufacture the hull-bounding input.

  ## Route 2: the image-degree hypothesis `hImage` (downgraded)

  * Under pointwise degree faithfulness `hdeg` and the packet contraction `q < 1`,
    `hImage` is a theorem
    (`sourceImageLogDegree_nonpos_of_degreeFaithful_and_q_lt_one`), by the existing
    value-realized theta-pilot log-volume formula of `SourceImageHullVolume.lean`.
  * Without `hdeg`, the local-compatibility chain of the contracted module needs the
    degree identity at nonzero labels only; the zero label is the unit point
    (`sourceThetaPilotPoint_zero_eq_one`), so
    `sourceImageLogDegree_nonpos_of_localCompatibility_nonzero_and_q_lt_one` drops the
    zero label from the compatibility hypothesis.
  * In its weakest useful form, the residual is the upper bound
    `degree <= card * log(theta_j)` at every label
    (`sourceImageLogDegree_nonpos_of_imageDegreeLe_and_q_lt_one`).

  ## The scaling hypothesis `hScaling` is refutable under degree faithfulness

  `not_sourceScalingUnits_logDegree_nonpos_of_degreeFaithful`: under `hdeg` the
  constant scaling of exponent `1` lies in `sourceScalingUnits` and has log-degree the
  index cardinality, which is positive; hence `hScaling` is false.  The conjunction of
  the two contracted-generator hypotheses is likewise refutable
  (`not_contractedGenerators_of_degreeFaithful`).  Consequently the hull bound cannot
  be pushed down to degree-level constraints in the regime where the value-level
  log-volume formulas hold; it remains the paper's ambient `O`-module / `1,circ U`
  compactness input (the named input of `SourceHullInterfaceDischarge.lean`, corpus
  lines 10408-10410).  The normalization context of the log-volume itself is
  [AbsTopIII], Proposition 5.7 (corpus lines 7915-7941).

  Corpus anchors: `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory
  III.txt`, lines 10351-10358, 10408-10410, 10895-10899.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui up um

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The paper's WLOG: a sign split of the target inequality -/

/-- Since `|log(q)| > 0` for a positive `q != 1`, the left side `-|log(q)|` of the
Corollary 3.12 inequality is strictly negative. -/
theorem neg_abs_log_lt_zero_of_pos_of_ne_one {q : Real} (hqpos : 0 < q)
    (hq1 : q ≠ 1) :
    -|Real.log q| < 0 :=
  neg_lt_zero.mpr (abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hqpos hq1))

/-- The trivial branch of the paper's WLOG: if `-|log(Theta)| >= 0`, then the target
`-|log(q)| <= -|log(Theta)|` holds because `-|log(q)| < 0` (corpus lines 10357-10358:
"an inequality -|log(Theta)| >= 0 would imply that -|log(Theta)| >= 0 > -|log(q)|"). -/
theorem neg_abs_log_le_of_nonneg_right {q Theta : Real} (hleft : -|Real.log q| < 0)
    (hright : 0 ≤ -|Real.log Theta|) :
    -|Real.log q| ≤ -|Real.log Theta| :=
  le_trans hleft.le hright

/-- **The paper's WLOG step, mechanized** (corpus lines 10354-10358): to prove the
target inequality `-|log(q)| <= -|log(Theta)|` it suffices to prove it in the strictly
negative branch `-|log(Theta)| < 0`; in the remaining branch the inequality is trivial.
No conjugation or positive-power transform is involved. -/
theorem neg_abs_log_le_of_wlog_negative_case {q Theta : Real}
    (hleft : -|Real.log q| < 0)
    (hmain : -|Real.log Theta| < 0 → -|Real.log q| ≤ -|Real.log Theta|) :
    -|Real.log q| ≤ -|Real.log Theta| := by
  rcases le_or_gt 0 (-|Real.log Theta|) with hnonneg | hneg
  · exact neg_abs_log_le_of_nonneg_right hleft hnonneg
  · exact hmain hneg

/-- The coefficient rider of the Corollary 3.12 statement (corpus lines 10352-10353
and 10895-10898): once `-|log(q)| <= -|log(Theta)|` is established, any coefficient
`C` with `-|log(Theta)| <= C * |log(q)|` satisfies `C >= -1`. -/
theorem coefficient_ge_neg_one_of_neg_abs_log_le {q Theta C : Real} (hqpos : 0 < q)
    (hq1 : q ≠ 1) (hle : -|Real.log q| ≤ -|Real.log Theta|)
    (hC : -|Real.log Theta| ≤ C * |Real.log q|) :
    -1 ≤ C := by
  have hpos : 0 < |Real.log q| :=
    abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hqpos hq1)
  have hmul : (-1 : Real) * |Real.log q| ≤ C * |Real.log q| := by
    calc (-1 : Real) * |Real.log q| = -|Real.log q| := by rw [neg_one_mul]
      _ ≤ -|Real.log Theta| := hle
      _ ≤ C * |Real.log q| := hC
  exact le_of_mul_le_mul_right hmul hpos

/-! ## 2. Instantiation at the source theta packet -/

/-- The paper's WLOG step at the actual source theta packet: the contraction
`q < 1` and the packet positivity give `|log(q)| > 0`, so the target inequality with
any `Theta` follows from its negative branch. -/
theorem sourceContractedPilotWlogReduction (v : V) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt (n.val : Int) 0).thetaPacket.q < 1) (Theta : Real)
    (hmain : -|Real.log Theta| < 0 →
      -|Real.log ((I.theaterAt (n.val : Int) 0).thetaPacket.q)| ≤ -|Real.log Theta|) :
    -|Real.log ((I.theaterAt (n.val : Int) 0).thetaPacket.q)| ≤ -|Real.log Theta| :=
  neg_abs_log_le_of_wlog_negative_case
    (neg_abs_log_lt_zero_of_pos_of_ne_one
      (I.theaterAt (n.val : Int) 0).thetaPacket.q_pos (ne_of_lt hq))
    hmain

/-- The coefficient rider at the actual source theta packet. -/
theorem sourceContractedPilotCoefficient_ge_neg_one (v : V) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt (n.val : Int) 0).thetaPacket.q < 1) (Theta C : Real)
    (hle : -|Real.log ((I.theaterAt (n.val : Int) 0).thetaPacket.q)| ≤
      -|Real.log Theta|)
    (hC : -|Real.log Theta| ≤
      C * |Real.log ((I.theaterAt (n.val : Int) 0).thetaPacket.q)|) :
    -1 ≤ C :=
  coefficient_ge_neg_one_of_neg_abs_log_le
    (I.theaterAt (n.val : Int) 0).thetaPacket.q_pos (ne_of_lt hq) hle hC

/-! ## 3. The image-degree residual -/

/-- The zero-labeled theta-pilot image point is the unit of the global value point
carrier: its theta special value is one, so its value-group element is `1`. -/
theorem sourceThetaPilotPoint_zero_eq_one (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceThetaPilotPoint v R n (zeroSignedLabel (l := l)) = 1 := by
  rw [I.sourceThetaPilotPoint_eq_constant v R n (zeroSignedLabel (l := l)),
    I.thetaValueAt_zero_eq_one v n, Real.log_one]
  funext p
  exact map_one R.posRealAction

/-- The image-degree hypothesis with the value-level compatibility required only at
nonzero labels: the zero label is discharged by the packet value `theta_0 = 1`
(`sourceThetaPilotPoint_zero_eq_one`), so the exact log-Kummer transcription is needed
only where the theta special value is a nontrivial power of the q-parameter. -/
theorem sourceImageLogDegree_nonpos_of_localCompatibility_nonzero_and_q_lt_one
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt (n.val : Int) 0).thetaPacket.q < 1)
    (hcompat : ∀ j : SignedLabel l.value, j.1 ≠ 0 →
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) =
        (Fintype.card (SourceVolumeIndex l) : Real) *
          Real.log (I.thetaValueAt (n.val : Int) 0 j)) :
    ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0 := by
  intro j
  by_cases hj : j.1 = 0
  · have hj' : j = zeroSignedLabel (l := l) :=
      Subtype.ext (by rw [hj, zeroSignedLabel_val])
    rw [hj', I.sourceThetaPilotPoint_zero_eq_one v R n]
    exact le_of_eq (I.sourceLocalLogDegree_one v)
  · rw [hcompat j hj]
    exact mul_nonpos_of_nonneg_of_nonpos
      (by exact_mod_cast (sourceVolumeIndex_card_pos l).le)
      (I.thetaValueAt_log_nonpos_of_q_lt_one v n j hq)

/-- **`hImage` discharged under degree faithfulness.**  If the value-realized
log-degree is faithful at every positive real exponent and the q-parameter is
contracted, the image-degree hypothesis holds outright: the theta-pilot log-volume
formula identifies the degree with the cardinality times the log of the theta special
value, whose log is nonpositive at every label. -/
theorem sourceImageLogDegree_nonpos_of_degreeFaithful_and_q_lt_one
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (hq : (I.theaterAt (n.val : Int) 0).thetaPacket.q < 1) :
    ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0 := by
  intro j
  rw [I.sourceLocalLogDegree_thetaPilotPoint v R n j hdeg]
  exact mul_nonpos_of_nonneg_of_nonpos
    (by exact_mod_cast (sourceVolumeIndex_card_pos l).le)
    (I.thetaValueAt_log_nonpos_of_q_lt_one v n j hq)

/-- The weakest form of the image-degree residual: an upper bound of the value-realized
log-degree by the cardinality times the log of the theta special value suffices; no
exact value-level log-Kummer identification is needed. -/
theorem sourceImageLogDegree_nonpos_of_imageDegreeLe_and_q_lt_one
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt (n.val : Int) 0).thetaPacket.q < 1)
    (hle : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤
        (Fintype.card (SourceVolumeIndex l) : Real) *
          Real.log (I.thetaValueAt (n.val : Int) 0 j)) :
    ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0 := by
  intro j
  exact le_trans (hle j) (mul_nonpos_of_nonneg_of_nonpos
    (by exact_mod_cast (sourceVolumeIndex_card_pos l).le)
    (I.thetaValueAt_log_nonpos_of_q_lt_one v n j hq))

/-! ## 4. The scaling hypothesis is refutable under degree faithfulness -/

/-- **Negative result.**  Under pointwise degree faithfulness the scaling hypothesis
`hScaling` of the contracted-source route is refutable: the constant scaling of
exponent `1` lies in `sourceScalingUnits` and has log-degree the index cardinality,
which is positive.  Hence the hull bound cannot be obtained from degree-level
constraints in the degree-faithful regime; it remains the paper's ambient `O`-module /
`1,circ U` compactness input (the named input of `SourceHullInterfaceDischarge`). -/
theorem not_sourceScalingUnits_logDegree_nonpos_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ (∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s ≤ 0) := by
  intro hScaling
  have hmem : I.constantThetaPilotPoint v R
      (Multiplicative.ofAdd (1 : Real)) ∈ I.sourceScalingUnits v :=
    I.constantThetaPilotPoint_mem_sourceScalingUnits v R (a := 1) one_ne_zero hdeg
  have hpos : 0 < I.sourceLocalLogDegree v
      (I.constantThetaPilotPoint v R (Multiplicative.ofAdd (1 : Real))) := by
    rw [I.sourceLocalLogDegree_constant v R 1 hdeg, mul_one]
    exact_mod_cast sourceVolumeIndex_card_pos l
  exact not_le_of_gt hpos (hScaling _ hmem)

/-- The conjunction of the two contracted-generator hypotheses is refutable under
pointwise degree faithfulness: `hImage` may hold, but `hScaling` cannot. -/
theorem not_contractedGenerators_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ (((∀ j : SignedLabel l.value,
        I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0) ∧
      (∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s ≤ 0))) :=
  fun h => I.not_sourceScalingUnits_logDegree_nonpos_of_degreeFaithful v R hdeg h.2

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the WLOG sign-split reduction and the downward push of the two
contraction residuals of the Card-HULLREAL contracted-source route. -/
def cardHullRealContractionWlogReduction : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-contraction-wlog"
    source :=
      "IUT III, Corollary 3.12 proof, lines 10351-10358 (statement and WLOG sign " ++
        "split), lines 10408-10410 (compactness of the 1,circ U), lines 10895-10899 " ++
        "(concluding inequality and C_Theta rider); [AbsTopIII], Proposition 5.7 " ++
        "(corpus lines 7915-7941)"
    status := VerificationStatus.interface
    note :=
      "Pushes down the two contraction residuals of " ++
        "SourceContractedSupplyRealization.lean: (1) the paper's WLOG is mechanized " ++
        "as a sign case split of the target inequality " ++
        "(neg_abs_log_le_of_wlog_negative_case, trivial branch " ++
        "neg_abs_log_le_of_nonneg_right, coefficient rider " ++
        "coefficient_ge_neg_one_of_neg_abs_log_le), instantiated at the source packet " ++
        "(sourceContractedPilotWlogReduction, " ++
        "sourceContractedPilotCoefficient_ge_neg_one); (2) the image-degree hypothesis " ++
        "hImage is discharged under pointwise degree faithfulness and q < 1 " ++
        "(sourceImageLogDegree_nonpos_of_degreeFaithful_and_q_lt_one), is reduced to " ++
        "compatibility at nonzero labels without degree faithfulness " ++
        "(sourceImageLogDegree_nonpos_of_localCompatibility_nonzero_and_q_lt_one, zero " ++
        "label via sourceThetaPilotPoint_zero_eq_one), and its weakest residual form is " ++
        "the upper bound degree <= card * log(theta_j) " ++
        "(sourceImageLogDegree_nonpos_of_imageDegreeLe_and_q_lt_one). Negative " ++
        "result: the scaling hypothesis hScaling is refutable under degree " ++
        "faithfulness (not_sourceScalingUnits_logDegree_nonpos_of_degreeFaithful; " ++
        "not_contractedGenerators_of_degreeFaithful), so the hull bound remains the " ++
        "paper's O-module/1,circ U compactness input."
    dependsOn :=
      [ "IUT-III.corollary-3.12-card-hullreal-contracted-source",
        "IUT-III.corollary-3.12-source-image-hull-volume",
        "IUT-III.corollary-3.12-iq-hull-interface-discharge" ] }

end LeanFormal.IUT.Audit
