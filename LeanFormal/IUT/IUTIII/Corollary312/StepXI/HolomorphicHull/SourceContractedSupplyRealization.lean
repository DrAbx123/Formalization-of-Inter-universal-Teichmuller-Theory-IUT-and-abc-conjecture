import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullInterfaceDischarge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceValueHullRealizationBridge
import LeanFormal.IUT.Audit.Status

/-!
  # Realized restrained sources for the Card-HULLREAL supplies

  The Card-HULLREAL bridge (`SourceValueHullRealizationBridge.lean`) consumes three
  source-side supplies at the fixed procession: the unit-region/Haar datum `D` (or
  the weaker finiteness `hfin`) and the label-wise theta contraction
  `thetaValueAt < 1`.  This module supplies real mathematical content for them from
  restrained (paper-shaped, source-level) inputs:

  * `thetaValueAt_lt_one_of_q_lt_one`: the q-contraction `q < 1` of the actual
    source theta packet, together with a nonzero label, gives the theta contraction
    at that label.  The Gaussian packet structure makes the special value the power
    `q^(j^2)` (`FiniteThetaPacket.scale_eq`, `log_scale`), so the single contraction
    constraint of the q-parameter drives every nonzero label.
  * `sourceHolomorphicHull_logDegree_nonpos_of_contractedGenerators`: if the image
    points of the theta-pilot object and every hull scaling have nonpositive
    log-degree, then the whole source holomorphic hull has nonpositive log-degree.
    Consequently the hull log-volume is finite
    (`sourceHullVolume_lt_top_of_contractedGenerators`) and the six fields of
    `SourceUnitRegionHaarData` are filled by proofs
    (`sourceContractedUnitRegionHaarData`), with the unit region the hull itself and
    the unit scaling `1`.
  * End-to-end consumption: the restrained inputs feed the bridge certificates and
    the `Cor312Conclusion` composition at both the canonical `q = -1` route
    (`sourceContractedPointWiringCor312Conclusion`) and the procession-normalized
    paper-`q` route (`sourceContractedNormalizedQ_cor312Conclusion`).

  Corpus anchors.  IUT III, Corollary 3.12 proof, Step (xi), and Remark 3.9.5, (i),
  (iii), in `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt`:

  * lines 10354-10360: the proof opens with `|log(q)| > 0` and the normalization
    convention `-|log(Theta)| < 0` (the nonpositive-degree regime formalized here).
  * lines 10381-10410: the collections `n,circ U_{j,vQ}` of unions of possible
    images and their holomorphic hulls; the key sentence at 10408-10410: "one
    concludes easily from the [easily verified] compactness of the 1,circ U_{j,vQ},
    together with the definition of the log-volume, that the quantity -|log(Theta)|
    is finite, hence negative".
  * lines 10751-10899: Substeps (xi-a) to (xi-f): the q-pilot object, the log-Kummer
    correspondence in the 1-column (10858), the `j`-normalized log-volume (10838),
    and the concluding inequality `-|log(q)| <= -|log(Theta)|` (10895-10899).
  * lines 7658-7750: Remark 3.9.5, (i): the hull `lambda.O` with every component of
    `lambda` nonzero; (iii) line 7743: all indeterminacies are compact, contained in
    the compact set `phi(P)`.

  [AbsTopIII] anchors, `papers/motizuki_corpus/text/Topics in Absolute Anabelian
  Geometry III.txt`:

  * lines 7915-7941: Proposition 5.7 (Local Volumes): uniqueness of the additive,
    translation-invariant, normalized volume `mu_k(O_k) = 1` on compact open subsets
    of a nonarchimedean local field; scaling law `mu_k^log(x.A) = mu_k^log(A) +
    x-dot-log`; invariance for units.

  Honesty boundary.  These results formalize a value-level sufficient contraction
  regime; they are not a formalization of the paper's compactness of the
  `1,circ U_{j,vQ}` nor of the `O`-module structure of `IQ(S±_{j+1}; n,circ D_vQ)`
  (which remains the named input of `SourceHullInterfaceDischarge`), and the
  nonpositive-degree constraints on the generators remain explicit hypotheses.
  Under `OriginalInput` alone the hull is unbounded
  (`sourceHolomorphicHull_logDegree_unbounded`), so no unconditional supply exists
  at this carrier; the contraction constraints isolate exactly the additional
  content.
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

/-! ## 1. The q-contraction at the source theta packet -/

/-- At a nonzero label, the q-contraction `q < 1` of the actual source theta packet
gives the label-wise theta contraction.  The special value is the Gaussian power
`q^(j^2)`; a nonzero label has exponent at least one, so a contracted q-parameter
drives it below one. -/
theorem thetaValueAt_lt_one_of_q_lt_one (v : V)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) (hj : j.1 ≠ 0)
    (hq : (I.theaterAt (n.val : Int) 0).thetaPacket.q < 1) :
    I.thetaValueAt (n.val : Int) 0 j < 1 := by
  change (I.theaterAt (n.val : Int) 0).thetaPacket.scale j < 1
  have hqpos : 0 < (I.theaterAt (n.val : Int) 0).thetaPacket.q :=
    (I.theaterAt (n.val : Int) 0).thetaPacket.q_pos
  have hlogq : Real.log ((I.theaterAt (n.val : Int) 0).thetaPacket.q) < 0 :=
    (Real.log_neg_iff hqpos).mpr hq
  have hpos2 : (0 : Int) < gaussExponent j.1 := by
    unfold gaussExponent
    exact sq_pos_of_ne_zero hj
  have hle1 : (1 : Int) ≤ gaussExponent j.1 := by omega
  have hg : 1 ≤ (gaussExponent j.1).toNat := by
    have hcast : (1 : Int) ≤ ((gaussExponent j.1).toNat : Int) := by
      rw [Int.toNat_of_nonneg (le_of_lt hpos2)]
      exact hle1
    exact_mod_cast hcast
  have hlog : Real.log ((I.theaterAt (n.val : Int) 0).thetaPacket.scale j) < 0 := by
    rw [(I.theaterAt (n.val : Int) 0).thetaPacket.log_scale j]
    exact mul_neg_of_pos_of_neg
      (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hg)) hlogq
  exact (Real.log_neg_iff
    ((I.theaterAt (n.val : Int) 0).thetaPacket.scale_pos j)).mp hlog

/-- The zero label has theta special value exactly one: the strict contraction fails
there, so the nonzero-label hypothesis of `thetaValueAt_lt_one_of_q_lt_one` cannot be
dropped. -/
theorem thetaValueAt_zero_eq_one (v : V) (n : ThetaPilotCarrier l) :
    I.thetaValueAt (n.val : Int) 0 (zeroSignedLabel (l := l)) = 1 := by
  change (I.theaterAt (n.val : Int) 0).thetaPacket.scale
      (zeroSignedLabel (l := l)) = 1
  rw [(I.theaterAt (n.val : Int) 0).thetaPacket.scale_eq
      (zeroSignedLabel (l := l)), zeroSignedLabel_val, realThetaValue_zero]

/-- The logarithm of the theta special value is nonpositive at every label whenever
the q-parameter is contracted: at the zero label the value is one, and at a nonzero
label it is strictly below one. -/
theorem thetaValueAt_log_nonpos_of_q_lt_one (v : V)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value)
    (hq : (I.theaterAt (n.val : Int) 0).thetaPacket.q < 1) :
    Real.log (I.thetaValueAt (n.val : Int) 0 j) ≤ 0 := by
  by_cases hj : j.1 = 0
  · have hj' : j = zeroSignedLabel (l := l) :=
      Subtype.ext (by rw [hj, zeroSignedLabel_val])
    simp [hj', I.thetaValueAt_zero_eq_one v n]
  · exact le_of_lt
      ((Real.log_neg_iff (I.thetaValueAt_pos (n.val) 0 j)).mpr
        (I.thetaValueAt_lt_one_of_q_lt_one v n j hj hq))

/-- The nonpositive image-degree hypothesis of the contracted-source route is itself
derived from two restrained inputs: the q-contraction and the identification of the
image point's realized log-degree with the `j`-normalized log of the theta special
value (the value-level transcription of the log-Kummer correspondence of Step
(xi-d); under pointwise degree faithfulness it is the existing
`sourceLocalLogDegree_thetaPilotPoint`). -/
theorem sourceImageLogDegree_nonpos_of_localCompatibility_and_q_lt_one (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt (n.val : Int) 0).thetaPacket.q < 1)
    (hcompat : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) =
        (Fintype.card (SourceVolumeIndex l) : ℝ) *
          Real.log (I.thetaValueAt (n.val : Int) 0 j)) :
    ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0 := by
  intro j
  rw [hcompat j]
  exact mul_nonpos_of_nonneg_of_nonpos
    (by exact_mod_cast (sourceVolumeIndex_card_pos l).le)
    (I.thetaValueAt_log_nonpos_of_q_lt_one v n j hq)

/-! ## 2. The contracted hull and the realized unit-region/Haar datum -/

/-- The submonoid of global value points of nonpositive log-degree.  It contains the
unit and is closed under multiplication by additivity of the log-degree, and it is
the candidate hull used to bound the contracted source hull. -/
def sourceNonpositiveLogDegreeSubmonoid (v : V) :
    Submonoid (I.ThetaPilotPoint v) where
  carrier := {x | I.sourceLocalLogDegree v x ≤ 0}
  one_mem' := le_of_eq (I.sourceLocalLogDegree_one v)
  mul_mem' := by
    intro x y hx hy
    show I.sourceLocalLogDegree v (x * y) ≤ 0
    rw [I.sourceLocalLogDegree_mul v x y]
    exact add_nonpos hx hy

/-- Under nonpositive log-degree of every theta-pilot image point and every hull
scaling, the whole source holomorphic hull has nonpositive log-degree.  The image
containment and the scaling stability make the nonpositive log-degree submonoid a
candidate hull, so the least candidate hull lands inside it. -/
theorem sourceHolomorphicHull_logDegree_nonpos_of_contractedGenerators (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hImage : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s ≤ 0) :
    ∀ x : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
        I.sourceLocalLogDegree v x ≤ 0 := by
  intro x hx
  have hH : CandidateHull (I.sourceScalingUnits v)
      (I.sourceNonpositiveLogDegreeSubmonoid v) := by
    intro s hs y hy
    show I.sourceLocalLogDegree v (s * y) ≤ 0
    rw [I.sourceLocalLogDegree_mul v s y]
    exact add_nonpos (hScaling s hs) hy
  have hS : I.possibleThetaPilotImageSet v R n ⊆
      (I.sourceNonpositiveLogDegreeSubmonoid v : Set (I.ThetaPilotPoint v)) := by
    intro y hy
    obtain ⟨j, rfl⟩ :=
      (mem_possibleThetaPilotImageSet_iff (I := I) v R n y).mp hy
    exact hImage j
  exact I.sourceHolomorphicHull_le v R n hH hS hx

/-- The hull log-volume is finite under the contracted generators. -/
theorem sourceHullVolume_lt_top_of_contractedGenerators (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hImage : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceHullVolume v R n < ⊤ :=
  I.sourceHullVolume_lt_top_of_hullBound v R n (C := 0)
    (I.sourceHolomorphicHull_logDegree_nonpos_of_contractedGenerators v R n
      hImage hScaling)

/-- The six fields of the unit-region/Haar datum, realized from the contracted
generators: the unit region is the source hull itself, the scaling is the unit `1`,
the log-degree bound is `0`, the containment is by the unit scaling, and both degree
conditions are the contracted-generator bounds. -/
def sourceContractedUnitRegionHaarData (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hImage : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s ≤ 0) :
    I.SourceUnitRegionHaarData v R n :=
  I.compactnessInput_to_sourceUnitRegionHaarData v R n
    { scaling := 1
      unitRegion := (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))
      degreeBound := 0
      hull_subset_scaledRegionImage := by
        intro x hx
        exact ⟨x, hx, (one_mul x).symm⟩
      unitRegion_logDegree_le :=
        I.sourceHolomorphicHull_logDegree_nonpos_of_contractedGenerators v R n
          hImage hScaling }
    (le_of_eq (I.sourceLocalLogDegree_one v))

/-- The realized `IQHullLogVolumeInterface` at the value carrier from the contracted
generators: source set log-volume, source hull, and the theta-pilot image union. -/
def sourceContractedHullInterface (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hImage : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s ≤ 0) :
    IQHullLogVolumeInterface (I.ThetaPilotPoint v) :=
  I.sourceUnitRegionHaarInterface v R n
    (I.sourceContractedUnitRegionHaarData v R n hImage hScaling)

/-! ## 3. End-to-end consumption at the bridge certificates -/

/-- The canonical `q = -1` certificate route, closed from the contracted generators:
the composed `Cor312Conclusion` of the bridge with the realized unit-region/Haar
data. -/
theorem sourceContractedPointWiringCor312Conclusion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hImage : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s ≤ 0)
    (j : SignedLabel l.value) (ipl she apt : Prop)
    (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((I.sourceUnitRegionHaarPointWiringCertificate v R n
          (I.sourceContractedUnitRegionHaarData v R n hImage hScaling) j).toContract
        (I.sourceUnitRegionHaarPointWiringLinkEvidence v R n
          (I.sourceContractedUnitRegionHaarData v R n hImage hScaling) j
          ipl she apt hipl hshe hapt)) :=
  I.sourceUnitRegionHaarPointWiringCor312Conclusion v R n
    (I.sourceContractedUnitRegionHaarData v R n hImage hScaling) j
    ipl she apt hipl hshe hapt

/-- The procession-normalized paper-`q` route, closed from the contracted generators
together with the q-contraction: the theta contraction is derived from `q < 1` at the
nonzero label. -/
theorem sourceContractedNormalizedQ_cor312Conclusion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hImage : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s ≤ 0)
    (j : SignedLabel l.value) (hj : j.1 ≠ 0)
    (hq : (I.theaterAt (n.val : Int) 0).thetaPacket.q < 1)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((I.sourceUnitRegionHaarNormalizedQ_certificate v R n
          (I.sourceContractedUnitRegionHaarData v R n hImage hScaling) j
          (I.thetaValueAt_lt_one_of_q_lt_one v n j hj hq)).toContract
        (I.sourceUnitRegionHaarNormalizedQ_linkEvidence v R n
          (I.sourceContractedUnitRegionHaarData v R n hImage hScaling) j
          (I.thetaValueAt_lt_one_of_q_lt_one v n j hj hq)
          ipl she apt hipl hshe hapt)) :=
  I.sourceUnitRegionHaarNormalizedQ_cor312Conclusion v R n
    (I.sourceContractedUnitRegionHaarData v R n hImage hScaling) j
    (I.thetaValueAt_lt_one_of_q_lt_one v n j hj hq)
    ipl she apt hipl hshe hapt

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the realized restrained sources of the Card-HULLREAL supplies:
the q-contraction route to the theta contraction, the contracted-generator route to
the hull finiteness and the unit-region/Haar datum, and the end-to-end composition at
the bridge certificates. -/
def cardHullRealContractedSource : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-contracted-source"
    source :=
      "IUT III, Corollary 3.12 proof, Step (xi) (corpus lines 10354-10899); " ++
        "Remark 3.9.5, (i), (iii) (corpus lines 7658-7750); [AbsTopIII], " ++
        "Proposition 5.7, (i) (corpus lines 7915-7941)"
    status := VerificationStatus.interface
    note :=
      "Realized restrained sources for the Card-HULLREAL supplies at the value " ++
        "carrier: (c) the label-wise theta contraction follows from the q-parameter " ++
        "contraction q < 1 at a nonzero label via the Gaussian packet power " ++
        "(thetaValueAt_lt_one_of_q_lt_one; the zero label value is one, " ++
        "thetaValueAt_zero_eq_one); (a)/(b) nonpositive log-degree of the image " ++
        "points and of the hull scalings makes the whole source hull nonpositive " ++
        "(sourceHolomorphicHull_logDegree_nonpos_of_contractedGenerators), so the " ++
        "hull volume is finite and the six unit-region/Haar fields are filled " ++
        "(sourceContractedUnitRegionHaarData) with unitRegion the hull, scaling 1, " ++
        "bound 0; the image-degree hypothesis is itself derived from the q " ++
        "contraction plus the local compatibility of the realized log-degree with " ++
        "the normalized theta log " ++
        "(sourceImageLogDegree_nonpos_of_localCompatibility_and_q_lt_one). " ++
        "End-to-end: the bridge certificates and the Cor312Conclusion at both the " ++
        "q = -1 and the paper normalized-q routes " ++
        "(sourceContractedPointWiringCor312Conclusion, " ++
        "sourceContractedNormalizedQ_cor312Conclusion). Not claimed: the paper's " ++
        "compactness of the 1,circ U_{j,vQ} or the O-module structure of " ++
        "IQ(S±; n,circ D_vQ) -- the contracted-generator constraints remain " ++
        "explicit hypotheses of the value-level sufficient regime."
    dependsOn :=
      [ "IUT-III.corollary-3.12-card-hullreal-value-bridge",
        "IUT-III.corollary-3.12-iq-carrier-haar-data",
        "IUT-III.corollary-3.12-source-image-hull-volume",
        "IUT-III.corollary-3.12-iq-hull-interface-discharge" ] }

end LeanFormal.IUT.Audit