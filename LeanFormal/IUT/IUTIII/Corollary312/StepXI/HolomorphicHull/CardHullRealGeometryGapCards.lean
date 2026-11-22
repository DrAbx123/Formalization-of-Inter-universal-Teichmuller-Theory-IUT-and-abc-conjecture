import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.OModuleCompactnessLayer
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.PadicLogShellModel
import LeanFormal.IUT.Audit.Status

/-!
  # The R3 gap items of the O-module compactness restart: feasible pieces and gap cards

  The O-module layer restart (`OModuleCompactnessLayer.lean`) named the paper's two
  premises.  Its gap card listed four missing items to *construct* them:
  (i) a topology on the carrier, (ii) the O-module (ring-of-integers) structure,
  (iii) the boundedness consequence "compact implies contained in some lambda.O",
  (iv) the finite index family realizing `1,circ U` as a finite union, together with
  the value-level collapse card (index family -> single labelled image set).

  This module processes each item (reduction-pass discipline):

  ## Verdicts and three-route checks

  * (i) Topology.  Route (a) put an arbitrary topology on the value carrier: any such
    topology is *unsourced* (the discrete topology would redefine compactness as
    finiteness) -- rejected as unfaithful.  Route (b) model layer: the norm topology
    of the existing test carriers (`CertificateHullWiring.lean:222`,
    `PadicLogShellModel.lean` on `Q_p`) -- available, reused below.  Route (c) the
    literal `IQ(S+-_{j+1}; n,circ D^vdash_{vQ})` topology: no such object exists in
    the tree -- gap card.
  * (ii) O-module structure.  Route (a) impose a ring/module structure on the value
    monoid: unsourced -- rejected.  Route (b) model layer: the unit ball `Z_p` of
    `Q_p` is `closedBall 0 1`, i.e. Mathlib's `PadicInt` with its ring structure,
    compact open (`PadicLogShellModel.lean:87-93` builds `padicUnitCompacts`), and
    the real model uses the scalar module action (`NormedSpace`); available, cited.
    Route (c) the paper's local-field ring of integers inside the IQ carrier: absent
    -- gap card.
  * (iii) Compact implies scaled region.  Route (a) on the value carrier: not even
    statable (no topology) -- rejected.  Route (b) model layer: proved here in two
    forms -- the general normed-space form
    `isCompact_subset_smul_closedBall_unit` and the non-archimedean multiplicative
    form `padic_isCompact_subset_smul_closedBall_unit` (a compact subset of `Q_p`
    lies in a `lambda`-multiple of `Z_p`; `lambda` a power of `p`).  Route (c) the
    literal carrier: blocked by (i)/(ii) -- gap card.
  * (iv) Finite index family.  Route (a) finiteness of the image union: already
    proved (`possibleThetaPilotImageSet_finite`, `HullVertexConvexityAssembly.lean`).
    Route (b) the explicit finite union form: proved here
    (`possibleThetaPilotImageSet_eq_iUnion_singleton`,
    `possibleThetaPilotImageSet_eq_biUnion_finset`).  Route (c) the original double
    index family `|Fl| x VQ`: the value realization indexes by the signed labels
    only (the `VQ` direction is absorbed into the fixed carrier `V`) -- gap card on
    the double-index reconstruction, recorded, not silently identified.
  * (b) Value-level collapse card.  The collapse is *lossless* at the level of the
    `1,circ U` image-containment premise: `possibleThetaPilotImageSet_subset_iff_forall_mem`
    (a subset condition on the single set is exactly the per-label condition), with
    the premise-facing wrapper `sourceOneCircUCompactness_image_subset_iff_forall`
    for the R3 datum of `OModuleCompactnessLayer.lean`.  The `VQ`-direction collapse
    itself has no tree object to recover to -- recorded as a design fact, not proved
    away.

  ## Corpus anchors

  * IUT III, Corollary 3.12 proof, Step (xi) (corpus lines 10405-10411): "[easily
    verified] compactness of the 1,circ U_{j,vQ} [where j in |Fl|, vQ in VQ] ...
    the quantity -|log(Theta)| is finite"; the index family named in (iv).
  * IUT III, Remark 3.9.5, (i) (corpus lines 7658-7750): relatively compact
    subsets; the holomorphic hull; the lambda.O scaling classes.
  * IUT III, Corollary 3.12 proof opening (corpus lines 10351-10358); [AbsTopIII],
    Proposition 5.7, (i) (corpus lines 7915-7941): the normalization regime.

  ## Consumers and seams

  Card-HULLREAL real-card (geometry/topology realization) -> the conditional
  hypotheses of `CertificateHullWiring.lean` (`iqHullCertificate` interface datum
  plus the two `ENNReal` bounds) -> Step-XI finite certificates -> the Corollary
  3.12 `q <= Theta` conclusion -> ABC.  The pieces proved here calibrate the
  *shapes* on the model layer (`Q_p`, normed spaces); they do not construct the
  source carrier.

  ## Honesty boundary

  * The `Q_p` statement is a model-layer statement: `O` appears as `Z_p`, the
    lambda-multiple as the scalar multiple; the log-volume normalization of
    [AbsTopIII] Proposition 5.7 and the IQ carrier are absent (as in
    `PadicLogShellModel.lean`).
  * The generic normed-space form has no IUT content by itself; it is the
    mechanism template for (iii).
  * No degree-faithfulness hypothesis is introduced anywhere; the value-level
    lemmas are unconditional statement-layer algebra and remain valid in every
    regime, including the one where the O-module premises are empty.
  * The Popper in-flight modules are not imported and not touched.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open scoped Pointwise

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. Item (iv) and the collapse card (b): the finite labelled union -/

/-- **Finite labelled union form of the image union.**  The union of the possible
images is the union of the singletons of the labelled theta-pilot points over the
(finite) type of signed labels: the value-level transcription of the finite family
of the paper's `1,circ U_{j,vQ}` (`j in |Fl|`; the `vQ` direction is carried by the
fixed place `v` of the realization).  Unconditional. -/
theorem possibleThetaPilotImageSet_eq_iUnion_singleton (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.possibleThetaPilotImageSet v R n =
      ⋃ j : SignedLabel l.value, {I.sourceThetaPilotPoint v R n j} := by
  rw [Set.iUnion_singleton_eq_range]
  ext x
  rw [I.mem_possibleThetaPilotImageSet_iff v R n x, Set.mem_range]
  exact exists_congr fun j => eq_comm

/-- **The finite union over the explicit label list.**  The same equality with the
index family written as `Finset.univ` of the signed labels, matching the paper's
"where `j` in `|Fl|`" form of the compactness input. -/
theorem possibleThetaPilotImageSet_eq_biUnion_finset (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.possibleThetaPilotImageSet v R n =
      ⋃ j ∈ (Finset.univ : Finset (SignedLabel l.value)),
        {I.sourceThetaPilotPoint v R n j} := by
  rw [I.possibleThetaPilotImageSet_eq_iUnion_singleton v R n]
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_univ j, hj⟩⟩
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    rcases Set.mem_iUnion.mp hj with ⟨_, hjt⟩
    exact Set.mem_iUnion.mpr ⟨j, hjt⟩

/-- **The collapse card, lossless direction.**  A subset condition on the single
image-union set is exactly the per-label membership condition: verifying the
`1,circ U` containment label by label loses nothing (and gains nothing).  This is
what makes the value-level collapse honest at the premise level. -/
theorem possibleThetaPilotImageSet_subset_iff_forall_mem (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (U : Set (I.ThetaPilotPoint v)) :
    I.possibleThetaPilotImageSet v R n ⊆ U ↔
      ∀ j : SignedLabel l.value, I.sourceThetaPilotPoint v R n j ∈ U := by
  constructor
  · intro h j
    exact h (I.sourceThetaPilotPoint_mem v R n j)
  · intro h x hx
    obtain ⟨j, rfl⟩ := (I.mem_possibleThetaPilotImageSet_iff v R n x).mp hx
    exact h j

/-- **Premise-facing form.**  The `oneCircU` field of the compactness premise
(`SourceOneCircUCompactness`, `OModuleCompactnessLayer.lean:165`) can equivalently
be checked at the individual labelled images: the value-level collapse is lossless
for the premise that drives the hull finiteness. -/
theorem sourceOneCircUCompactness_image_subset_iff_forall (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (C : I.SourceOneCircUCompactness v R n) :
    I.possibleThetaPilotImageSet v R n ⊆ C.oneCircU ↔
      ∀ j : SignedLabel l.value, I.sourceThetaPilotPoint v R n j ∈ C.oneCircU :=
  I.possibleThetaPilotImageSet_subset_iff_forall_mem v R n C.oneCircU

end OriginalInput
end Theorem311Source

/-! ## 2. Item (iii): compact implies a scaled region, model layer -/

/-- **Item (iii), general normed form.**  A compact subset of a real normed space is
contained in a positive scalar multiple of the closed unit ball: the mechanism
template behind the paper's "compactness of `1,circ U` implies containment in some
`lambda.O`".  No IUT content is claimed; this calibrates the shape on the model
layer. -/
theorem isCompact_subset_smul_closedBall_unit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ R • Metric.closedBall (0 : E) 1 := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨1, one_pos, Set.empty_subset _⟩
  · obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hK.isBounded
    have hC0 : 0 ≤ C := by
      have h := hC hx₀ hx₀
      rwa [dist_self] at h
    have hRpos : 0 < C + ‖x₀‖ + 1 := by
      have := norm_nonneg x₀
      linarith
    refine ⟨C + ‖x₀‖ + 1, hRpos, ?_⟩
    intro x hx
    have hxR : ‖x‖ ≤ C + ‖x₀‖ := by
      have h1 : dist x x₀ ≤ C := hC hx hx₀
      have htri : dist x (0 : E) ≤ dist x x₀ + dist x₀ (0 : E) :=
        dist_triangle x x₀ 0
      have h4 : dist x (0 : E) = ‖x‖ := by rw [dist_eq_norm, sub_zero]
      have h3 : dist x₀ (0 : E) = ‖x₀‖ := by rw [dist_eq_norm, sub_zero]
      linarith
    rw [Set.mem_smul_set]
    refine ⟨(C + ‖x₀‖ + 1)⁻¹ • x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr hRpos.le)]
      calc (C + ‖x₀‖ + 1)⁻¹ * ‖x‖
          ≤ (C + ‖x₀‖ + 1)⁻¹ * (C + ‖x₀‖ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hRpos.le)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hRpos)
    · exact smul_inv_smul₀ (ne_of_gt hRpos) x

/-- **Item (iii), non-archimedean multiplicative form.**  A compact subset of `Q_p`
is contained in a `lambda`-multiple of the unit ball `Z_p = closedBall 0 1` (the
model of the paper's `O`), with `lambda` an inverse power of `p`: the `lambda.O`
scaling shape realized on the local-field model of `PadicLogShellModel.lean`.  The
scalar is a `Q_p`-element here (multiplicative action), unlike the log-domain
translation picture of the existing file. -/
theorem padic_isCompact_subset_smul_closedBall_unit (p : ℕ) [Fact p.Prime]
    {K : Set ℚ_[p]} (hK : IsCompact K) :
    ∃ lam : ℚ_[p], K ⊆ lam • Metric.closedBall (0 : ℚ_[p]) 1 := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, Set.empty_subset _⟩
  · obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hK.isBounded
    have hC0 : 0 ≤ C := by
      have h := hC hx₀ hx₀
      rwa [dist_self] at h
    have hxR : ∀ x ∈ K, ‖x‖ ≤ C + ‖x₀‖ := by
      intro x hx
      have h1 : dist x x₀ ≤ C := hC hx hx₀
      have htri : dist x (0 : ℚ_[p]) ≤ dist x x₀ + dist x₀ (0 : ℚ_[p]) :=
        dist_triangle x x₀ 0
      have h4 : dist x (0 : ℚ_[p]) = ‖x‖ := by rw [dist_eq_norm, sub_zero]
      have h3 : dist x₀ (0 : ℚ_[p]) = ‖x₀‖ := by rw [dist_eq_norm, sub_zero]
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (C + ‖x₀‖)
    have hnp : (n : ℝ) ≤ (p : ℝ) ^ n := by
      have h1 : (n : ℝ) ≤ (2 : ℝ) ^ n := by
        exact_mod_cast (Nat.le_of_lt n.lt_two_pow_self)
      have h2 : (2 : ℝ) ^ n ≤ (p : ℝ) ^ n :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast (Fact.out : p.Prime).two_le) n
      linarith
    have hpne : (p : ℚ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hlamne : ((p : ℚ_[p])⁻¹) ^ n ≠ 0 :=
      pow_ne_zero n (inv_ne_zero hpne)
    have hnormlam : ‖((p : ℚ_[p])⁻¹) ^ n‖ = (p : ℝ) ^ n := by
      rw [norm_pow, norm_inv, Padic.norm_p, inv_inv]
    refine ⟨((p : ℚ_[p])⁻¹) ^ n, ?_⟩
    intro x hx
    have hxle : ‖x‖ ≤ (p : ℝ) ^ n := le_trans (hxR x hx) (lt_of_lt_of_le hn hnp).le
    rw [Set.mem_smul_set]
    refine ⟨(((p : ℚ_[p])⁻¹) ^ n)⁻¹ • x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, hnormlam]
      calc ((p : ℝ) ^ n)⁻¹ * ‖x‖
          ≤ ((p : ℝ) ^ n)⁻¹ * ((p : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left hxle (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg p) n))
        _ = 1 := inv_mul_cancel₀ (pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
    · exact smul_inv_smul₀ hlamne x

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the R3 gap-item processing of the Card-HULLREAL O-module
restart: the item-wise verdicts, the proved finite-union/collapse lemmas, and the
two model-layer forms of "compact implies a scaled region". -/
def cardHullRealGeometryGapCards : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-geometry-gap-cards"
    source :=
      "IUT III, Corollary 3.12 proof, Step (xi) (corpus lines 10405-10411); " ++
        "Remark 3.9.5, (i) (corpus lines 7658-7750); Corollary 3.12 proof " ++
        "opening (corpus lines 10351-10358); [AbsTopIII], Proposition 5.7, (i) " ++
        "(corpus lines 7915-7941)"
    status := VerificationStatus.provedKernel
    note :=
      "R3 item processing. Proved: (iv)+(b) the finite labelled-union forms of " ++
        "the possible-image set and the lossless per-label form of the 1,circ U " ++
        "containment premise (possibleThetaPilotImageSet_eq_iUnion_singleton, " ++
        "possibleThetaPilotImageSet_eq_biUnion_finset, " ++
        "possibleThetaPilotImageSet_subset_iff_forall_mem, " ++
        "sourceOneCircUCompactness_image_subset_iff_forall); (iii) the model-layer " ++
        "boundedness consequence in a general real normed space " ++
        "(isCompact_subset_smul_closedBall_unit) and on Q_p with O = Z_p and " ++
        "multiplicative scaling by a p-power " ++
        "(padic_isCompact_subset_smul_closedBall_unit). Gap cards (recorded in the " ++
        "module docstring, not constructed): (i) carrier topology, (ii) " ++
        "ring-of-integers module structure on the carrier, and the double-index " ++
        "family |Fl| x VQ; the VQ direction is absorbed in the fixed place v of the " ++
        "value realization. Model cases only: no IQ carrier, no [AbsTopIII] " ++
        "normalization; no degree-faithfulness hypothesis."
    dependsOn :=
      [ "IUT-III.corollary-3.12-card-hullreal-omodule-compactness",
        "IUT-III.corollary-3.12-padic-log-shell-model",
        "IUT-III.corollary-3.12-source-image-hull-volume" ] }

end LeanFormal.IUT.Audit