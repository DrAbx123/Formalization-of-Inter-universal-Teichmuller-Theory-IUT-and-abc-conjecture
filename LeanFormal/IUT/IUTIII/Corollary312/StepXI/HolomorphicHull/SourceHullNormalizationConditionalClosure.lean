import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullVertexConvexityAssembly
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# Card A conditional closure: the frozen hull normalization comparison

Task `hunit-epsilon-transfer-20261016`, Card A slice (see
`logs/coordination/hunit-epsilon-transfer-20261016.md`, sections 6 and 12).
The frozen proposition is the sharp normalization comparison behind the
`hunit` input of the Corollary 3.12 gap assembly,

  `ENNReal.ofReal D.degreeBound <= I.sourceHullVolume v R n + ENNReal.ofReal D0`

together with its epsilon form, with the consumer chain
`Cor312ComparisonGapSupplyLayer.lean:167` (the `hB` input) ->
`Cor312ComparisonGapReduction.lean:367-393` (the `hunit` operand of
`cor312GapAssembly_epsilonComparisonOfReducedInputs`) ->
`Cor312ToABCBridgeInterface.lean:247-250/:329-334` (the gap-2 field
`regionVolume_le_normalizedWeight`).  Paper anchor: IUT III, Corollary 3.12
(log-volume estimates for Theta-pilot objects; corpus
`Inter-universal Teichmuller Theory III.txt:10324-10358`), Remark 3.9.5,
(i)-(iii).

This file (1) freezes the comparison as a conditional datum with exactly the
two named hypotheses required by the task -- a true unit-region/Haar carrier
datum and the hull bound -- and wires the existing consumer interfaces
(`cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume`,
`..._of_epsilon_hullBound` of `HunitEpsilonTransferReduction.lean`), and
(2) records three routes on the two hypotheses themselves:

* Route R1 (discharge the carrier hypothesis): fails.  No construction exists
  in the tree, and under pointwise degree faithfulness the datum space is
  empty (`cor312SourceHullNormalizationData_not_nonempty_of_degreeFaithful`),
  on O1 `sourceHullVolume_eq_top_of_degreeFaithful`
  (`SourceImageHullVolume.lean:428`) against the carrier-forced finiteness
  `sourceUnitRegionHaarInterface_hull_logVolume_lt_top` (`IQCarrierHaarData.lean:207`).
* Route R2 (discharge the hull bound from the interface fields): fails, and
  the fields in fact prove the reverse inequality
  (`sourceHullVolume_le_ofReal_of_unitRegionHaarData`): the hull sits below
  the degree bound, contraction included.  The frozen comparison is a genuine
  lower bound for the hull volume -- the geometric content of Corollary 3.12
  (Remark 3.9.5, (iii)) -- and cannot follow from the interface fields.
* Route R3 (replace the hull volume term by the vertex term, using the
  compiled Card B wiring): succeeds as a sufficient substitute.  The
  vertex-checked and finite-label checked data
  (`Cor312SourceHullVertexCheckedData`, `Cor312SourceHullLabelEpsilonCheckedData`)
  close the same conclusion through the proved Card B interfaces
  (`HullVertexConvexityAssembly.lean`); the substitute is strictly stronger
  (it implies the hull bound by monotonicity), and no converse replacement is
  available.

Honesty labels: every closure in this file is conditional on the named datum;
no true carrier is constructed and the geometric normalization content of
route (iii) remains open.  The epsilon shape is the comparison-layer
reshaping of the companion file, not a paper statement.  The conditional
datum space is vacuous under degree faithfulness, so the closure must not be
read as non-vacuous progress in that regime.  No frozen file is modified.
-/

namespace LeanFormal.IUT

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. Route R2: the interface fields prove the reverse inequality -/

/-- **Reverse-direction pin (route R2).**  The fields of the unit-region/Haar
datum alone prove that the hull log-volume is at most the degree bound: the
hull is contained in the scaled unit region, the scaling has nonpositive
log-degree (contraction), and the unit region is bounded by `degreeBound`.
The frozen obligation needs the opposite direction -- a lower bound for the
hull volume -- so the hull bound cannot be discharged from the interface
fields; that direction is exactly the geometric content of Corollary 3.12
(Remark 3.9.5, (iii)).  This is the precise negative content of route R2. -/
theorem sourceHullVolume_le_ofReal_of_unitRegionHaarData (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) :
    I.sourceHullVolume v R n ≤ ENNReal.ofReal D.degreeBound := by
  unfold sourceHullVolume
  calc I.sourceSetVolume v
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))
      ≤ I.sourceSetVolume v (scaledRegionImage D.scaling D.unitRegion) :=
        I.sourceSetVolume_mono v D.hull_subset_scaledRegionImage
    _ ≤ I.sourceSetVolume v D.unitRegion :=
        I.sourceSetVolume_scaledRegionImage_le_of_nonpos_logDegree v
          D.scaling_logDegree_nonpos
    _ ≤ ENNReal.ofReal D.degreeBound :=
        I.sourceSetVolume_le_ofReal_of_logDegree_le v D.unitRegion_logDegree_le

/-! ## 2. The frozen conditional data and closure at the consumer site -/

/-- **Frozen conditional datum (sharp form).**  The two named hypotheses of
the frozen comparison: an actual unit-region/Haar carrier datum `carrier`, and
the hull bound `ofReal carrier.degreeBound <= sourceHullVolume + ofReal D0`
consumed as `hB` by
`cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume`
(`Cor312ComparisonGapSupplyLayer.lean:167`).  No construction of a datum of
this shape is provided anywhere in this file. -/
structure Cor312SourceHullNormalizationData (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (D₀ : ℝ) where
  /-- The true-carrier hypothesis: a unit-region/Haar datum. -/
  carrier : I.SourceUnitRegionHaarData v R n
  /-- The normalization constant is nonnegative (the consumer's `hD0`). -/
  hD₀ : 0 ≤ D₀
  /-- The hull bound: the frozen comparison itself. -/
  hullBound : ENNReal.ofReal carrier.degreeBound ≤
    I.sourceHullVolume v R n + ENNReal.ofReal D₀

/-- **Frozen conditional datum (epsilon form).**  The epsilon-shaped version
of `Cor312SourceHullNormalizationData`, matching the consumer drop-in
`cor312GapSupply_sourceInterface_hunit_of_epsilon_hullBound`
(`HunitEpsilonTransferReduction.lean:118`); the two shapes have the same
satisfiability space (conversions below). -/
structure Cor312SourceHullNormalizationEpsilonData (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) (D₀ : ℝ) where
  /-- The true-carrier hypothesis: a unit-region/Haar datum. -/
  carrier : I.SourceUnitRegionHaarData v R n
  /-- The normalization constant is nonnegative. -/
  hD₀ : 0 ≤ D₀
  /-- The per-epsilon hull bound. -/
  hullBoundε : ∀ ε : NNReal, 0 < ε →
    ENNReal.ofReal carrier.degreeBound ≤
      I.sourceHullVolume v R n + ENNReal.ofReal D₀ + (ε : ENNReal)

/-- **Conditional closure (sharp form).**  The frozen datum closes the hunit
input of the gap assembly through the frozen consumer
`cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume`
(`Cor312ComparisonGapSupplyLayer.lean:167`); the conclusion is exactly the
`hunit` operand of `cor312GapAssembly_epsilonComparisonOfReducedInputs`
(`Cor312ComparisonGapReduction.lean:376`). -/
theorem cor312SourceHullNormalizationData_hunit (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {D₀ : ℝ}
    (C : Cor312SourceHullNormalizationData (I := I) v R n D₀) :
    (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
        (I.sourceUnitRegionHaarInterface v R n C.carrier).unitRegion ≤
      (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
          (I.sourceUnitRegionHaarInterface v R n C.carrier).hull +
        ENNReal.ofReal D₀ :=
  I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume v R n
    C.carrier C.hD₀ C.hullBound

/-- **Conditional closure (epsilon form).**  The epsilon-shaped datum closes
the same hunit input through the epsilon drop-in
`cor312GapSupply_sourceInterface_hunit_of_epsilon_hullBound`
(`HunitEpsilonTransferReduction.lean:118`). -/
theorem cor312SourceHullNormalizationEpsilonData_hunit (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {D₀ : ℝ}
    (C : Cor312SourceHullNormalizationEpsilonData (I := I) v R n D₀) :
    (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
        (I.sourceUnitRegionHaarInterface v R n C.carrier).unitRegion ≤
      (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
          (I.sourceUnitRegionHaarInterface v R n C.carrier).hull +
        ENNReal.ofReal D₀ :=
  I.cor312GapSupply_sourceInterface_hunit_of_epsilon_hullBound v R n
    C.carrier C.hD₀ C.hullBoundε

/-- **Data-level sharp-to-epsilon conversion.**  The sharp datum gives the
epsilon datum (transfer `cor312GapSupply_forall_pos_le_add_of_le`), so the
epsilon closure is available for every sharp datum. -/
def cor312SourceHullNormalizationData_toEpsilonData (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {D₀ : ℝ}
    (C : Cor312SourceHullNormalizationData (I := I) v R n D₀) :
    Cor312SourceHullNormalizationEpsilonData (I := I) v R n D₀ where
  carrier := C.carrier
  hD₀ := C.hD₀
  hullBoundε := cor312GapSupply_forall_pos_le_add_of_le C.hullBound

/-- **Data-level epsilon-to-sharp conversion.**  The epsilon datum gives the
sharp datum (transfer `cor312GapSupply_le_of_forall_pos_le_add`): the two
datum shapes have the same satisfiability space. -/
def cor312SourceHullNormalizationEpsilonData_toData (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {D₀ : ℝ}
    (C : Cor312SourceHullNormalizationEpsilonData (I := I) v R n D₀) :
    Cor312SourceHullNormalizationData (I := I) v R n D₀ where
  carrier := C.carrier
  hD₀ := C.hD₀
  hullBound := cor312GapSupply_le_of_forall_pos_le_add C.hullBoundε

/-! ## 3. Route R3: vertex- and label-checked substitutes -/

/-- **Vertex-checked substitute datum (route R3, sharp form).**  The hull
bound with the hull volume term replaced by the (smaller) log-volume of the
union of the possible theta-pilot images; since the hull contains the image
union (`sourceHullVolume_ge_imageVolume`, `SourceImageHullVolume.lean:209`),
this check implies the hull bound and is a sufficient, strictly stronger
hypothesis.  The converse replacement (hull check implies vertex check) is
not available. -/
structure Cor312SourceHullVertexCheckedData (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (D₀ : ℝ) where
  /-- The true-carrier hypothesis: a unit-region/Haar datum. -/
  carrier : I.SourceUnitRegionHaarData v R n
  /-- The normalization constant is nonnegative. -/
  hD₀ : 0 ≤ D₀
  /-- The vertex check: the bound against the image-union log-volume. -/
  vertexBound : ENNReal.ofReal carrier.degreeBound ≤
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) + ENNReal.ofReal D₀

/-- **Conditional closure from the vertex check (route R3).**  Wires the
Card B interface `cor312GapSupply_sourceInterface_hunit_of_vertexVolumeBound`
(`HullVertexConvexityAssembly.lean`). -/
theorem cor312SourceHullVertexCheckedData_hunit (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {D₀ : ℝ}
    (C : Cor312SourceHullVertexCheckedData (I := I) v R n D₀) :
    (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
        (I.sourceUnitRegionHaarInterface v R n C.carrier).unitRegion ≤
      (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
          (I.sourceUnitRegionHaarInterface v R n C.carrier).hull +
        ENNReal.ofReal D₀ :=
  I.cor312GapSupply_sourceInterface_hunit_of_vertexVolumeBound v R n
    C.carrier C.hD₀ C.vertexBound

/-- **Substitution pin (route R3).**  The vertex check implies the hull bound
by monotonicity of the sup-type volume: this is the precise sense in which
the Card B wiring replaces the hull volume term in the frozen comparison. -/
def cor312SourceHullVertexCheckedData_toNormalizationData (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {D₀ : ℝ}
    (C : Cor312SourceHullVertexCheckedData (I := I) v R n D₀) :
    Cor312SourceHullNormalizationData (I := I) v R n D₀ where
  carrier := C.carrier
  hD₀ := C.hD₀
  hullBound := le_trans C.vertexBound
    (add_le_add (I.sourceHullVolume_ge_imageVolume v R n)
      (le_refl (ENNReal.ofReal D₀)))

/-- **Finite-label checked substitute datum (route R3, epsilon form).**  The
epsilon-shaped version with the check performed at the finitely many signed
labels (`sourceSetVolume_possibleImageSet_eq_labelSup`), matching the Card B
interface `cor312GapSupply_sourceInterface_hunit_of_labelEpsilonBound`. -/
structure Cor312SourceHullLabelEpsilonCheckedData (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) (D₀ : ℝ) where
  /-- The true-carrier hypothesis: a unit-region/Haar datum. -/
  carrier : I.SourceUnitRegionHaarData v R n
  /-- The normalization constant is nonnegative. -/
  hD₀ : 0 ≤ D₀
  /-- The finite signed-label check. -/
  labelBoundε : ∀ ε : NNReal, 0 < ε →
    ENNReal.ofReal carrier.degreeBound ≤
      (⨆ j : SignedLabel l.value,
        ENNReal.ofReal (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j))) +
        ENNReal.ofReal D₀ + (ε : ENNReal)

/-- **Conditional closure from the finite-label check (route R3).**  Wires
the Card B interface
`cor312GapSupply_sourceInterface_hunit_of_labelEpsilonBound`
(`HullVertexConvexityAssembly.lean`); this is the finite "verify only at the
vertices" form of the frozen obligation. -/
theorem cor312SourceHullLabelEpsilonCheckedData_hunit (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {D₀ : ℝ}
    (C : Cor312SourceHullLabelEpsilonCheckedData (I := I) v R n D₀) :
    (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
        (I.sourceUnitRegionHaarInterface v R n C.carrier).unitRegion ≤
      (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
          (I.sourceUnitRegionHaarInterface v R n C.carrier).hull +
        ENNReal.ofReal D₀ :=
  I.cor312GapSupply_sourceInterface_hunit_of_labelEpsilonBound v R n
    C.carrier C.hD₀ C.labelBoundε

/-! ## 4. Route R1 pins: finiteness and emptiness under degree faithfulness -/

/-- **The carrier forces a finite hull volume.**  Every datum of the frozen
shape carries the finiteness of the hull log-volume through the interface
(`sourceUnitRegionHaarInterface_hull_logVolume_lt_top`,
`IQCarrierHaarData.lean:207`); together with O1
(`sourceHullVolume_eq_top_of_degreeFaithful`, `SourceImageHullVolume.lean:428`)
this is the structural reason why the conditional datum is unavailable under
degree faithfulness. -/
theorem cor312SourceHullNormalizationData_hullVolume_lt_top (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {D₀ : ℝ}
    (C : Cor312SourceHullNormalizationData (I := I) v R n D₀) :
    I.sourceHullVolume v R n < ⊤ :=
  I.sourceUnitRegionHaarInterface_hull_logVolume_lt_top v R n C.carrier

/-- **Route R1 negative result: the datum space is empty under degree
faithfulness.**  The carrier would force a finite hull log-volume, while
degree faithfulness forces the hull log-volume to be `⊤` (O1).  Hence no
`D0` carries the frozen conditional datum in that regime; the conditional
closure is vacuous exactly there. -/
theorem cor312SourceHullNormalizationData_not_nonempty_of_degreeFaithful
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) (D₀ : ℝ)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ Nonempty (Cor312SourceHullNormalizationData (I := I) v R n D₀) := by
  rintro ⟨C⟩
  have hfin : I.sourceHullVolume v R n < ⊤ :=
    I.sourceUnitRegionHaarInterface_hull_logVolume_lt_top v R n C.carrier
  rw [I.sourceHullVolume_eq_top_of_degreeFaithful v R n hdeg] at hfin
  exact (lt_irrefl (⊤ : ENNReal)) hfin

/-! ## 5. Consumer-site composite: the GapReduction wire -/

/-- **Consumer-site composite.**  The frozen datum together with the four
remaining named inputs of `cor312GapAssembly_epsilonComparisonOfReducedInputs`
(`Cor312ComparisonGapReduction.lean:367-393`) specialized to the carrier
interface produces the `Cor312EpsilonArithmeticComparison` record; the
`hunit` operand is supplied by `cor312SourceHullNormalizationData_hunit`,
and the produced gap-2 field has the ToABCBridge consumer shape
(`Cor312ToABCBridgeInterface.lean:247-250`, `:331-334`).  The remaining named
inputs are hypotheses, unchanged; no gap field is filled. -/
noncomputable def cor312SourceHullNormalizationData_epsilonComparison (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {D₀ : ℝ}
    (C : Cor312SourceHullNormalizationData (I := I) v R n D₀)
    (logShellPoint : Nat → Nat → Nat → I.ThetaPilotPoint v)
    {eps D₁ : ℝ} (heps : 0 ≤ eps)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) ≤ 1 + eps)
    (hweightvol : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        ((I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
          (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n C.carrier)
            logShellPoint a b c)).toReal)
    (hsplit : ∀ a b c : Nat, IsABCTriple a b c →
      (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
          (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n C.carrier)
            logShellPoint a b c) ≤
        (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
            ((I.sourceUnitRegionHaarInterface v R n C.carrier).scaleShift ''
              (I.sourceUnitRegionHaarInterface v R n C.carrier).unitRegion) +
          (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
            {(I.sourceUnitRegionHaarInterface v R n C.carrier).scaleShift
              (logShellPoint a b c)})
    (hptfin : ∀ a b c : Nat, IsABCTriple a b c →
      (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
        {(I.sourceUnitRegionHaarInterface v R n C.carrier).scaleShift
          (logShellPoint a b c)} < ⊤)
    (hpoint : ∀ a b c : Nat, IsABCTriple a b c →
      ((I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
        {(I.sourceUnitRegionHaarInterface v R n C.carrier).scaleShift
          (logShellPoint a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁) :
    Cor312EpsilonArithmeticComparison
      (I.sourceUnitRegionHaarInterface v R n C.carrier) eps :=
  cor312GapAssembly_epsilonComparisonOfReducedInputs
    (I.sourceUnitRegionHaarInterface v R n C.carrier)
    logShellPoint heps C.hD₀ hval hweightvol
    (cor312SourceHullNormalizationData_hunit (I := I) v R n C)
    hsplit hptfin hpoint

end OriginalInput
end Theorem311Source

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the Card A conditional closure: the frozen hull
normalization comparison as a conditional datum, its closures at the consumer
site, and the three-route outcomes on the two hypotheses. -/
def cor312HullNormalizationConditionalClosure : Obligation :=
  { id := "IUT-III.cor312-hull-normalization-conditional-closure"
    source :=
      "IUT III, Corollary 3.12 (normalized log-volume comparison of the " ++
        "holomorphic hull; corpus lines 10324-10358); Remark 3.9.5, (i)-(iii); " ++
        "consumer chain Cor312ComparisonGapSupplyLayer.lean:167 -> " ++
        "Cor312ComparisonGapReduction.lean:367-393 -> " ++
        "Cor312ToABCBridgeInterface.lean:247-250/:329-334"
    status := VerificationStatus.interface
    note :=
      "Card A slice of hunit-epsilon-transfer-20261016. CONDITIONAL CLOSURE: " ++
        "the frozen comparison ofReal D.degreeBound <= sourceHullVolume + " ++
        "ofReal D0 is packaged as Cor312SourceHullNormalizationData (carrier + " ++
        "hull bound) and its epsilon form; cor312SourceHullNormalizationData_hunit " ++
        "and cor312SourceHullNormalizationEpsilonData_hunit wire the frozen " ++
        "consumer SupplyLayer:167 and the epsilon drop-in; the composite " ++
        "cor312SourceHullNormalizationData_epsilonComparison supplies the hunit " ++
        "operand of GapReduction:367-393 with the remaining named inputs as " ++
        "hypotheses. ROUTE OUTCOMES: R1 (carrier) fails -- the datum space is " ++
        "empty under degree faithfulness " ++
        "(cor312SourceHullNormalizationData_not_nonempty_of_degreeFaithful, on O1 " ++
        "sourceHullVolume_eq_top_of_degreeFaithful and the carrier-forced " ++
        "finiteness); R2 (bound from the interface fields) fails -- the fields " ++
        "prove the reverse inequality " ++
        "(sourceHullVolume_le_ofReal_of_unitRegionHaarData); R3 (vertex-term " ++
        "replacement via the proved Card B wiring) succeeds as a sufficient, " ++
        "strictly stronger substitute (Cor312SourceHullVertexCheckedData, " ++
        "Cor312SourceHullLabelEpsilonCheckedData with closures and the " ++
        "substitution pin), not as a discharge. NOT proved: any true-carrier " ++
        "datum; the geometric lower bound for the hull volume (route (iii)) " ++
        "remains open, and the conditional space is vacuous under degree " ++
        "faithfulness."
    dependsOn :=
      [ "IUT-III.cor312-hunit-epsilon-transfer"
      , "IUT-III.cor312-hull-vertex-convexity-assembly"
      , "IUT-III.cor312-comparison-gap-reduction"
      , "IUT-III.corollary-3.12-iq-carrier-haar-data"
      , "IUT-III.corollary-3.12-source-image-hull-volume" ] }

end LeanFormal.IUT.Audit
