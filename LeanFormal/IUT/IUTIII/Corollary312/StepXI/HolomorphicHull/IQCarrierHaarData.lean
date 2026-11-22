import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring

/-!
  # Unit-region/Haar data layer for the value-realized IQ carrier

  The discharge audit `Audit.iqHullInterfaceDischarge` records that no realization of
  `IQHullLogVolumeInterface` for the actual `IQ(S±_{j+1}; n,◦D^vdash_{vQ})` carrier is
  available in the tree, and that the minimal sufficient addition is the carrier-level
  unit-region/Haar datum.  This module isolates that datum for the value-realized
  carrier `I.ThetaPilotPoint v` of `SourceImageHull.lean` /
  `SourceImageHullVolume.lean` and relates it exactly to the interface:

  * Conditional implementation (`SourceUnitRegionHaarData`,
    `sourceUnitRegionHaarInterface`): a unit region `O` (the role of the log-shell
    region `O_{vQ}`), a scaling `lambda`, a log-degree bound on `O`, the paper-shaped
    containment `hull ⊆ lambda·O`, and the value-level Haar-normalization direction
    `logDegree lambda ≤ 0` (contraction: scaling does not increase the log-volume, the
    analogue of `q_contracting`) realize `IQHullLogVolumeInterface` on the carrier
    with `logVolume := sourceSetVolume v`.  From the data the hull log-volume is
    finite and normalized lower bounds transfer to the hull; the data is exactly the
    named `ValueHullCompactnessInput` plus the contraction field.
  * Exact reduction: `sourceSetVolume_lt_top_iff_exists_logDegree_le` shows that at
    the value level finiteness of the log-volume of a region is equivalent to
    boundedness of its log-degree, and
    `exists_iqHullLogVolumeInterface_hull_iff_exists_logDegree_le` shows that an
    interface realization whose `logVolume` is the source set log-volume and whose
    hull is the actual source hull exists if and only if the hull is log-degree
    bounded (the backward direction is the unit-scaling interface
    `sourceHullUnitScalingInterface`; the forward direction is the interface's own
    finiteness field).
  * Obstruction: under pointwise degree faithfulness no such interface with a hull
    containing the source hull exists
    (`not_exists_iqHullLogVolumeInterface_hull_subset_of_degreeFaithful`), so a
    direct implementation of the finiteness field on the actual hull is refuted at
    this level of realization without additional carrier data.
  * Cross-wire: `sourceUnitRegionHaarData_cor312Conclusion` feeds the data through
    `CertificateHullWiring` to `Cor312Conclusion`.

  Honesty note: with the hull field pinned to the actual hull the volume carries
  content; an interface with `logVolume := sourceSetVolume v` and a trivial hull
  exists vacuously, so the pinning of the hull is essential.  Nothing here is
  claimed to follow from `OriginalInput`: `SourceUnitRegionHaarData` is additional
  named data, and the NOT-proved statement of `Audit.iqHullInterfaceDischarge`
  remains open.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe ua uv upi umon ui up um

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. Volume-level lemmas for the value-realized carrier -/

/-- The image of a set under the multiplicative translation `x ↦ lam * x` is the scaled
region `lam·O` of Remark 3.9.5, (i). -/
theorem image_mul_eq_scaledRegionImage {P : Type um} [CommMonoid P] (lam : P)
    (O : Set P) :
    (fun x : P => lam * x) '' O = scaledRegionImage lam O := by
  ext x
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, h.symm⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, h.symm⟩

/-- The log-volume of a region of value points is at most the `ENNReal.ofReal` of any
real log-degree bound of the region. -/
theorem sourceSetVolume_le_ofReal_of_logDegree_le (v : V)
    {O : Set (I.ThetaPilotPoint v)} {C : ℝ}
    (hO : ∀ y ∈ O, I.sourceLocalLogDegree v y ≤ C) :
    I.sourceSetVolume v O ≤ ENNReal.ofReal C := by
  unfold sourceSetVolume
  refine iSup_le_iff.mpr fun x => ?_
  refine iSup_le_iff.mpr fun hx => ?_
  exact ENNReal.ofReal_le_ofReal (hO x hx)

/-- The multiplicative translation by a scaling of nonpositive log-degree does not
increase the log-volume: the value-level Haar-normalization direction (contraction) of
the scaling regions of Remark 3.9.5, (i). -/
theorem sourceSetVolume_scaledRegionImage_le_of_nonpos_logDegree (v : V)
    {lam : I.ThetaPilotPoint v} {O : Set (I.ThetaPilotPoint v)}
    (hlam : I.sourceLocalLogDegree v lam ≤ 0) :
    I.sourceSetVolume v (scaledRegionImage lam O) ≤ I.sourceSetVolume v O := by
  unfold sourceSetVolume
  refine iSup_le_iff.mpr fun x => ?_
  refine iSup_le_iff.mpr fun hx => ?_
  obtain ⟨y, hy, rfl⟩ := (mem_scaledRegionImage_iff).mp hx
  have hle : I.sourcePointVolume v (lam * y) ≤ I.sourcePointVolume v y := by
    change ENNReal.ofReal (I.sourceLocalLogDegree v (lam * y)) ≤
      ENNReal.ofReal (I.sourceLocalLogDegree v y)
    rw [I.sourceLocalLogDegree_mul v lam y]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact le_trans hle (le_iSup_of_le y (le_iSup_of_le hy le_rfl))

/-- **Exact reduction, region form.**  A region of value points has finite log-volume
if and only if it is bounded in log-degree. -/
theorem sourceSetVolume_lt_top_iff_exists_logDegree_le (v : V)
    (O : Set (I.ThetaPilotPoint v)) :
    I.sourceSetVolume v O < ⊤ ↔
      ∃ C : ℝ, ∀ y ∈ O, I.sourceLocalLogDegree v y ≤ C := by
  constructor
  · intro hfin
    refine ⟨(I.sourceSetVolume v O).toReal, fun y hy => ?_⟩
    have hle :
        ENNReal.ofReal (I.sourceLocalLogDegree v y) ≤ I.sourceSetVolume v O := by
      unfold sourceSetVolume
      exact le_iSup_of_le y (le_iSup_of_le hy le_rfl)
    have h1 : (ENNReal.ofReal (I.sourceLocalLogDegree v y)).toReal ≤
        (I.sourceSetVolume v O).toReal :=
      ENNReal.toReal_mono hfin.ne hle
    have h2 : I.sourceLocalLogDegree v y ≤
        (ENNReal.ofReal (I.sourceLocalLogDegree v y)).toReal := by
      by_cases h0 : 0 ≤ I.sourceLocalLogDegree v y
      · exact le_of_eq (ENNReal.toReal_ofReal h0).symm
      · exact le_trans (le_of_lt (not_le.mp h0)) ENNReal.toReal_nonneg
    exact le_trans h2 h1
  · rintro ⟨C, hC⟩
    exact lt_of_le_of_lt (I.sourceSetVolume_le_ofReal_of_logDegree_le v hC)
      ENNReal.ofReal_lt_top

/-- The hull log-volume is finite exactly when the hull is bounded in log-degree (the
converse direction of `sourceHullVolume_lt_top_of_hullBound`). -/
theorem sourceHullVolume_lt_top_iff_exists_hullLogDegree_le (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n < ⊤ ↔
      ∃ C : ℝ, ∀ x : I.ThetaPilotPoint v,
        x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
          I.sourceLocalLogDegree v x ≤ C :=
  I.sourceSetVolume_lt_top_iff_exists_logDegree_le v
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))

/-! ## 2. The unit-region/Haar data and the interface it realizes -/

/-- **Unit-region/Haar data for the value-realized IQ carrier.**  The exact additional
data beyond `OriginalInput` that realizes `IQHullLogVolumeInterface` on the value
carrier with the source log-volume: a unit region `unitRegion` (the role of the
ring-of-integers/log-shell region `O_{vQ}`), a scaling `scaling` (the role of the
`lambda` of the `lambda·O` regions of Remark 3.9.5, (i)), a log-degree bound on the
unit region, the paper-shaped containment of the hull in the scaled unit region, and
the value-level Haar-normalization direction `scaling_logDegree_nonpos`: the scaling
has nonpositive log-degree, so `scaling` does not increase the log-volume
(contraction, the analogue of `q_contracting`).  None of the fields is claimed to
follow from `OriginalInput`; under pointwise degree faithfulness no such datum exists
for the source hull
(`not_exists_iqHullLogVolumeInterface_hull_subset_of_degreeFaithful`). -/
structure SourceUnitRegionHaarData (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) where
  /-- The unit region `O` (the role of the log-shell region `O_{vQ}`). -/
  unitRegion : Set (I.ThetaPilotPoint v)
  /-- The scaling `lambda` of the `lambda·O` region. -/
  scaling : I.ThetaPilotPoint v
  /-- The log-degree bound on the unit region. -/
  degreeBound : ℝ
  /-- The hull is contained in the `lambda`-multiple of the unit region. -/
  hull_subset_scaledRegionImage :
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
      scaledRegionImage scaling unitRegion
  /-- Every point of the unit region has log-degree at most the bound. -/
  unitRegion_logDegree_le :
    ∀ y ∈ unitRegion, I.sourceLocalLogDegree v y ≤ degreeBound
  /-- The value-level Haar-normalization direction: the scaling has nonpositive
  log-degree, so scaling does not increase the log-volume. -/
  scaling_logDegree_nonpos : I.sourceLocalLogDegree v scaling ≤ 0

/-- The `IQHullLogVolumeInterface` realized by the value carrier from the
unit-region/Haar data: `logVolume` is the source set log-volume, the hull is the
source holomorphic hull, and `scaleShift` is the multiplicative scaling. -/
def sourceUnitRegionHaarInterface (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (D : I.SourceUnitRegionHaarData v R n) :
    IQHullLogVolumeInterface (I.ThetaPilotPoint v) where
  imageSet := I.possibleThetaPilotImageSet v R n
  hull := (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))
  imageSet_subset_hull := I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n
  logVolume := I.sourceSetVolume v
  logVolume_mono := fun hST => I.sourceSetVolume_mono v hST
  unitRegion := D.unitRegion
  scaleShift := fun x => D.scaling * x
  hull_subset_scaleShift := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ :=
      (mem_scaledRegionImage_iff).mp (D.hull_subset_scaledRegionImage hx)
    exact ⟨y, hy, hxy.symm⟩
  unitRegion_logVolume_lt_top :=
    lt_of_le_of_lt
      (I.sourceSetVolume_le_ofReal_of_logDegree_le v D.unitRegion_logDegree_le)
      ENNReal.ofReal_lt_top
  scaleShift_unitRegion_logVolume_le := by
    rw [image_mul_eq_scaledRegionImage]
    exact I.sourceSetVolume_scaledRegionImage_le_of_nonpos_logDegree v
      D.scaling_logDegree_nonpos

/-- The hull log-volume of the value carrier is finite under the unit-region/Haar
data. -/
theorem sourceUnitRegionHaarInterface_hull_logVolume_lt_top (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) :
    I.sourceHullVolume v R n < ⊤ :=
  (I.sourceUnitRegionHaarInterface v R n D).hull_logVolume_lt_top

/-- The normalized lower bound transfers through the interface: any lower bound on
the image-union log-volume is a lower bound of the finite hull log-volume. -/
theorem sourceUnitRegionHaarInterface_lower_bound_and_finiteness (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) {lowerBound : ENNReal}
    (h : lowerBound ≤ I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)) :
    lowerBound ≤ I.sourceHullVolume v R n ∧ I.sourceHullVolume v R n < ⊤ :=
  (I.sourceUnitRegionHaarInterface v R n D).lower_bound_and_finiteness h

/-- The unit-region/Haar data restricts to the named value-level compactness input of
`SourceHullInterfaceDischarge` (the same unit region, scaling and bound, forgetting
the contraction direction). -/
def sourceUnitRegionHaarData_to_compactnessInput (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) :
    I.ValueHullCompactnessInput v R n where
  scaling := D.scaling
  unitRegion := D.unitRegion
  degreeBound := D.degreeBound
  hull_subset_scaledRegionImage := D.hull_subset_scaledRegionImage
  unitRegion_logDegree_le := D.unitRegion_logDegree_le

/-- Conversely, the value-level compactness input together with the contraction
direction of its scaling is exactly the unit-region/Haar data. -/
def compactnessInput_to_sourceUnitRegionHaarData (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (H : I.ValueHullCompactnessInput v R n)
    (hlam : I.sourceLocalLogDegree v H.scaling ≤ 0) :
    I.SourceUnitRegionHaarData v R n where
  unitRegion := H.unitRegion
  scaling := H.scaling
  degreeBound := H.degreeBound
  hull_subset_scaledRegionImage := H.hull_subset_scaledRegionImage
  unitRegion_logDegree_le := H.unitRegion_logDegree_le
  scaling_logDegree_nonpos := hlam

/-- The compactness input plus the contraction direction gives finiteness of the hull
log-volume through the interface route. -/
theorem sourceHullVolume_lt_top_of_compactnessInput_and_contraction (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (H : I.ValueHullCompactnessInput v R n)
    (hlam : I.sourceLocalLogDegree v H.scaling ≤ 0) :
    I.sourceHullVolume v R n < ⊤ :=
  I.sourceUnitRegionHaarInterface_hull_logVolume_lt_top v R n
    (I.compactnessInput_to_sourceUnitRegionHaarData v R n H hlam)

/-! ## 3. Exact reduction: interface existence versus hull boundedness -/

/-- The unit-scaling interface on the source hull: the unit region is the hull itself
and the scaling is the monoid unit (log-degree `0`), so the Haar-normalization field
holds by the contraction lemma.  It exists exactly when the hull log-volume is
finite. -/
def sourceHullUnitScalingInterface (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (hfin : I.sourceHullVolume v R n < ⊤) :
    IQHullLogVolumeInterface (I.ThetaPilotPoint v) where
  imageSet := I.possibleThetaPilotImageSet v R n
  hull := (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))
  imageSet_subset_hull := I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n
  logVolume := I.sourceSetVolume v
  logVolume_mono := fun hST => I.sourceSetVolume_mono v hST
  unitRegion := (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))
  scaleShift := fun x => (1 : I.ThetaPilotPoint v) * x
  hull_subset_scaleShift := by
    intro x hx
    exact ⟨x, hx, one_mul x⟩
  unitRegion_logVolume_lt_top := hfin
  scaleShift_unitRegion_logVolume_le := by
    rw [image_mul_eq_scaledRegionImage]
    exact I.sourceSetVolume_scaledRegionImage_le_of_nonpos_logDegree v
      (le_of_eq (I.sourceLocalLogDegree_one v))

/-- **Exact reduction.**  An `IQHullLogVolumeInterface` realization on the value
carrier whose log-volume is the source set log-volume and whose hull is the actual
source holomorphic hull exists if and only if the hull is bounded in log-degree. -/
theorem exists_iqHullLogVolumeInterface_hull_iff_exists_logDegree_le (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (∃ W : IQHullLogVolumeInterface (I.ThetaPilotPoint v),
        W.logVolume = I.sourceSetVolume v ∧
        W.hull = (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))) ↔
      ∃ C : ℝ, ∀ x : I.ThetaPilotPoint v,
        x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
          I.sourceLocalLogDegree v x ≤ C := by
  constructor
  · rintro ⟨W, hvol, hhull⟩
    have hfin : I.sourceHullVolume v R n < ⊤ := by
      have h := W.hull_logVolume_lt_top
      rw [hvol, hhull] at h
      exact h
    exact (I.sourceHullVolume_lt_top_iff_exists_hullLogDegree_le v R n).mp hfin
  · rintro ⟨C, hC⟩
    have hfin : I.sourceHullVolume v R n < ⊤ :=
      (I.sourceHullVolume_lt_top_iff_exists_hullLogDegree_le v R n).mpr ⟨C, hC⟩
    exact ⟨I.sourceHullUnitScalingInterface v R n hfin, rfl, rfl⟩

/-! ## 4. Obstruction under degree faithfulness -/

/-- Under pointwise degree faithfulness no interface realization on the value carrier
whose log-volume is the source set log-volume and whose hull contains the source
holomorphic hull exists: its finiteness field would contradict
`sourceHullVolume_eq_top_of_degreeFaithful`. -/
theorem not_exists_iqHullLogVolumeInterface_hull_subset_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ ∃ W : IQHullLogVolumeInterface (I.ThetaPilotPoint v),
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆ W.hull ∧
        W.logVolume = I.sourceSetVolume v := by
  rintro ⟨W, hsub, hvol⟩
  have hle : I.sourceHullVolume v R n ≤ W.logVolume W.hull := by
    unfold sourceHullVolume
    rw [← hvol]
    exact W.logVolume_mono hsub
  have htop : (⊤ : ENNReal) ≤ W.logVolume W.hull := by
    rw [← I.sourceHullVolume_eq_top_of_degreeFaithful v R n hdeg]
    exact hle
  exact not_lt_of_ge htop W.hull_logVolume_lt_top

/-- The pinned form: under degree faithfulness there is no interface whose log-volume
is the source set log-volume and whose hull is exactly the source hull (the left-hand
side of the exact reduction), so both sides of
`exists_iqHullLogVolumeInterface_hull_iff_exists_logDegree_le` fail in that regime. -/
theorem not_exists_iqHullLogVolumeInterface_hull_eq_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ ∃ W : IQHullLogVolumeInterface (I.ThetaPilotPoint v),
        W.logVolume = I.sourceSetVolume v ∧
        W.hull = (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
  rintro ⟨W, hvol, hhull⟩
  refine (I.not_exists_iqHullLogVolumeInterface_hull_subset_of_degreeFaithful v R n
    hdeg) ⟨W, ?_, hvol⟩
  intro x hx
  rwa [hhull]

/-! ## 5. Cross-wire to the Step-XI finite certificate consumer -/

/-- The unit-region/Haar data of the source carrier feeds the Step-XI finite
certificate of `CertificateHullWiring` directly: any finite labeling of the image
union with nonnegative weighted data and the named hypotheses on `q, theta` and the
`IPL`/`SHE`/`APT` evidence yields `Cor312Conclusion` through the existing assembly. -/
theorem sourceUnitRegionHaarData_cor312Conclusion {label : Type up} [Fintype label]
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (pt : label → I.ThetaPilotPoint v)
    (hpt : ∀ i, pt i ∈ I.possibleThetaPilotImageSet v R n)
    (data : WeightedValues label)
    (hvalue : ∀ i, data.value i =
      (iqHullFiniteHull (I.sourceUnitRegionHaarInterface v R n D) pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i) (q θ : ℝ)
    (hq : ENNReal.ofReal q ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n))
    (hθ : I.sourceHullVolume v R n ≤ ENNReal.ofReal θ)
    (hθ0 : 0 ≤ θ) (hqneg : q < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((iqHullCertificate (I.sourceUnitRegionHaarInterface v R n D) pt hpt data hvalue
          hw q θ hq hθ hθ0 hqneg).toContract
        (iqHullLinkEvidence (I.sourceUnitRegionHaarInterface v R n D) pt hpt data hvalue
          hw q θ hq hθ hθ0 hqneg ipl she apt hipl hshe hapt)) :=
  iqHullCor312Conclusion (I.sourceUnitRegionHaarInterface v R n D) pt hpt data hvalue hw
    q θ hq hθ hθ0 hqneg ipl she apt hipl hshe hapt

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the unit-region/Haar data layer of the value-realized IQ
carrier. -/
def iqCarrierHaarData : Obligation :=
  { id := "IUT-III.corollary-3.12-iq-carrier-haar-data"
    source :=
      "IUT III, Corollary 3.12 proof (compactness of the 1,circ U_{j,vQ} and the " ++
        "definition of the log-volume); Remark 3.9.5, (i), (ii)"
    status := VerificationStatus.interface
    note :=
      "Unit-region/Haar data layer for the value-realized IQ carrier. Conditional: " ++
        "SourceUnitRegionHaarData (unit region O, scaling lam, log-degree bound on O, " ++
        "hull subset lam*O, contraction logDegree lam <= 0) realizes " ++
        "IQHullLogVolumeInterface on I.ThetaPilotPoint v with logVolume = sourceSetVolume v; " ++
        "corollaries: hull log-volume finite, normalized lower-bound transfer, and the " ++
        "data equals ValueHullCompactnessInput plus the contraction field. Exact reduction: " ++
        "sourceSetVolume_lt_top_iff_exists_logDegree_le (finite volume iff log-degree " ++
        "bounded) and exists_iqHullLogVolumeInterface_hull_iff_exists_logDegree_le " ++
        "(interface with the source log-volume and the actual source hull exists iff the " ++
        "hull is log-degree bounded; backward via sourceHullUnitScalingInterface). " ++
        "Obstruction: under pointwise degree faithfulness no such interface with a hull " ++
        "containing the source hull exists, so a direct implementation of the finiteness " ++
        "field on the actual hull is refuted at this level of realization. NOT proved: a " ++
        "realization of the interface from OriginalInput; the data layer is additional " ++
        "named data. Cross-wire: sourceUnitRegionHaarData_cor312Conclusion feeds the " ++
        "Step-XI finite certificate via CertificateHullWiring. Honesty note: the pinning " ++
        "of the hull field to the actual hull carries the content; with a trivial hull an " ++
        "interface with this logVolume exists vacuously."
    dependsOn :=
      [ "IUT-III.corollary-3.12-iq-hull-log-volume-interface",
        "IUT-III.corollary-3.12-iq-hull-interface-discharge",
        "IUT-III.corollary-3.12-source-image-hull-volume",
        "IUT-III.corollary-3.12-step-XI-certificate-hull-wiring" ] }

end LeanFormal.IUT.Audit
