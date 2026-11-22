import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer

/-!
# Epsilon reshaping of the hunit normalization obligation (comparison layer)

Task `hunit-epsilon-transfer-20261016`, deliverable 1.  The consumer of the
reshaped form is `cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume`
(`ABCBridge/Bridge/Cor312ComparisonGapSupplyLayer.lean:167`), which reduces the
`hunit` input of the Corollary 3.12 gap assembly to the sharp normalization
comparison `ofReal D.degreeBound <= sourceHullVolume v R n + ofReal D0`
(the `hB` hypothesis of that theorem).

Paper anchors (IUT III, Corollary 3.12, "Log-volume Estimates for Theta-Pilot
Objects", corpus `Inter-universal Teichmuller Theory III.txt:10324-10338`: the
procession-normalized mono-analytic log-volume of the holomorphic hull
`[cf. Remark 3.9.5, (i)]` of the union of the possible images of a Theta-pilot
object; `|log(q)| > 0` at :10349-10351; the WLOG normalization
`-|log(Theta)| < 0` in the proof at :10354-10358).  The paper states no epsilon
form of this normalization comparison; the reshaping below is a
proof-technique-level device corresponding to the epsilon-absorption pattern of
"Explicit estimates in IUTeich", Lemma 1.11 (linearization of logarithms,
:897-903) applied with `a = xi/(6(1+xi))` in Proposition 1.12 (:906-935).  The
reshaping provably changes no content: the epsilon form and the sharp form have
the same satisfiability space
(`cor312GapSupply_exists_epsilon_hullBound_iff_exists_degreeBound_le_hullVolume`).

Honesty labels:
* The epsilon transfer is comparison-layer only: it produces no geometric
  content and does not prove `hunit`; it only lets a producer discharge the
  obligation in the per-epsilon shape.
* Carrier-satisfiability antecedent: the obligation (sharp or epsilon) needs a
  unit-region/Haar datum `D`, and under pointwise degree faithfulness no such
  datum exists
  (`cor312GapSupply_not_exists_epsilon_hullBound_of_degreeFaithful` below,
  pinning the frozen refutations
  `not_nonempty_valueHullCompactnessInput_of_degreeFaithful`
  (`SourceHullInterfaceDischarge.lean:232`) and
  `iqCarrierModel_sourceHaarData_not_nonempty_of_degreeFaithful`
  (`IQCarrierConcreteModel.lean:565`)).  The reshaping does not repair this.
* Route (i) of `carrier-normalization-crosscheck-20261016.md:107` is assembled
  below as a conditional form
  (`cor312GapSupply_sourceInterface_hunit_unitRegion_subset_hull`): the
  additional carrier containment `unitRegion subset hull` closes `hunit` with
  `D0 = 0` by monotonicity of the sup-type volume.  That containment is not a
  field of the frozen `SourceUnitRegionHaarData` and is not the paper's route;
  the geometric normalization comparison (route (iii)) remains open.

Scope: comparison layer and conditional assembly over the frozen interfaces;
no frozen file is modified.
-/

namespace LeanFormal.IUT

universe ua uv upi umon ui

/-- **Epsilon-to-sharp transfer for `ENNReal` comparisons.**  If `a <= b + eps`
for every positive `eps : NNReal`, then `a <= b`.  This is
`ENNReal.le_of_forall_pos_le_add` (`Data/ENNReal/Basic.lean:611`) with the
finiteness premise `b < infinity` removed from the producer's hypothesis: the
case `b = infinity` is trivial and the Mathlib lemma covers the rest
internally. -/
theorem cor312GapSupply_le_of_forall_pos_le_add {a b : ENNReal}
    (h : ∀ ε : NNReal, 0 < ε → a ≤ b + (ε : ENNReal)) : a ≤ b :=
  ENNReal.le_of_forall_pos_le_add fun ε hε _ => h ε hε

/-- **Sharp-to-epsilon transfer.**  If `a <= b`, then `a <= b + eps` for every
positive `eps : NNReal`.  Together with
`cor312GapSupply_le_of_forall_pos_le_add` this shows the two comparison shapes
are equivalent: the reshaping neither weakens nor strengthens an obligation. -/
theorem cor312GapSupply_forall_pos_le_add_of_le {a b : ENNReal} (h : a ≤ b) :
    ∀ ε : NNReal, 0 < ε → a ≤ b + (ε : ENNReal) := fun ε _ =>
  le_trans h (by simp)

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- **Epsilon form of the hunit normalization comparison (reshaping lemma).**
The obligation reshaped by sketch A of `outsider-survey-estimates-20261016.md`
(:145-156): under the per-epsilon comparison of the degree bound against the
hull volume, the sharp comparison `hB` of
`cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume`
(`Cor312ComparisonGapSupplyLayer.lean:167`) holds.  The unused hypothesis `_hD0` is carried to match
the plug-in shape of the consumer; the transfer itself does not consume it.
This is a comparison-layer reshape only, with no geometric content, and is not
`hunit` itself; it is content-preserving by
`cor312GapSupply_exists_epsilon_hullBound_iff_exists_degreeBound_le_hullVolume`. -/
theorem cor312GapSupply_hunit_of_epsilon_hullBound (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) {D₀ : ℝ} (_hD₀ : 0 ≤ D₀)
    (hε : ∀ ε : NNReal, 0 < ε →
      ENNReal.ofReal D.degreeBound ≤
        I.sourceHullVolume v R n + ENNReal.ofReal D₀ + (ε : ENNReal)) :
    ENNReal.ofReal D.degreeBound ≤
      I.sourceHullVolume v R n + ENNReal.ofReal D₀ :=
  cor312GapSupply_le_of_forall_pos_le_add hε

/-- **Converse of the reshaping lemma.**  The sharp comparison implies its
per-epsilon form, so the epsilon-shaped obligation is exactly as strong as the
sharp one. -/
theorem cor312GapSupply_epsilon_hullBound_of_hunit (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) {D₀ : ℝ} (_hD₀ : 0 ≤ D₀)
    (hB : ENNReal.ofReal D.degreeBound ≤
      I.sourceHullVolume v R n + ENNReal.ofReal D₀) :
    ∀ ε : NNReal, 0 < ε →
      ENNReal.ofReal D.degreeBound ≤
        I.sourceHullVolume v R n + ENNReal.ofReal D₀ + (ε : ENNReal) :=
  cor312GapSupply_forall_pos_le_add_of_le hB

/-- **Consumer drop-in: the epsilon form of the hunit input.**  Same conclusion
as `cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume`
(`Cor312ComparisonGapSupplyLayer.lean:167`), with the sharp comparison `hB`
replaced by its per-epsilon form.  This is the theorem a geometric producer
(route (iii)) can feed with epsilon-absorbed estimates. -/
theorem cor312GapSupply_sourceInterface_hunit_of_epsilon_hullBound (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) {D₀ : ℝ} (hD₀ : 0 ≤ D₀)
    (hε : ∀ ε : NNReal, 0 < ε →
      ENNReal.ofReal D.degreeBound ≤
        I.sourceHullVolume v R n + ENNReal.ofReal D₀ + (ε : ENNReal)) :
    (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).unitRegion ≤
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
          (I.sourceUnitRegionHaarInterface v R n D).hull + ENNReal.ofReal D₀ :=
  I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume v R n D hD₀
    (I.cor312GapSupply_hunit_of_epsilon_hullBound v R n D hD₀ hε)

/-- **Satisfiability space of the reshaped obligation.**  For a fixed
normalization constant `D0 >= 0`, the carrier data satisfying the epsilon form
are exactly those satisfying the sharp comparison: the reshaping changes the
obligation's shape, not its satisfiability.  By
`cor312GapSupply_not_exists_epsilon_hullBound_of_degreeFaithful` the common
space can be empty; the reshaping does not repair that.  The conditional
calibration model of `IQCarrierConcreteModel.lean`
(`iqCarrierModel_hunit_unitRegion`, `iqCarrierModel_hunit_degreeBound`,
:303/:315) satisfies the sharp form on its own carrier; it is a calibration
instance, not the paper carrier. -/
theorem cor312GapSupply_exists_epsilon_hullBound_iff_exists_degreeBound_le_hullVolume
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {D₀ : ℝ} (hD₀ : 0 ≤ D₀) :
    (∃ D : I.SourceUnitRegionHaarData v R n,
        ∀ ε : NNReal, 0 < ε →
          ENNReal.ofReal D.degreeBound ≤
            I.sourceHullVolume v R n + ENNReal.ofReal D₀ + (ε : ENNReal)) ↔
      (∃ D : I.SourceUnitRegionHaarData v R n,
        ENNReal.ofReal D.degreeBound ≤
          I.sourceHullVolume v R n + ENNReal.ofReal D₀) := by
  constructor
  · rintro ⟨D, hε⟩
    exact ⟨D, I.cor312GapSupply_hunit_of_epsilon_hullBound v R n D hD₀ hε⟩
  · rintro ⟨D, hB⟩
    exact ⟨D, I.cor312GapSupply_epsilon_hullBound_of_hunit v R n D hD₀ hB⟩

/-- **Carrier-satisfiability antecedent, pinned to the epsilon form.**  Under
pointwise degree faithfulness the epsilon-form obligation has no carrier:
there is no `SourceUnitRegionHaarData`, hence no instance of the reshaped
hypothesis either.  Reuses the frozen refutations
`not_nonempty_valueHullCompactnessInput_of_degreeFaithful`
(`SourceHullInterfaceDischarge.lean:232`) and
`iqCarrierModel_sourceHaarData_not_nonempty_of_degreeFaithful`
(`IQCarrierConcreteModel.lean:565`); it records that the reshaping creates no
carrier where none exists. -/
theorem cor312GapSupply_not_exists_epsilon_hullBound_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) (D₀ : ℝ)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ ∃ D : I.SourceUnitRegionHaarData v R n,
        ∀ ε : NNReal, 0 < ε →
          ENNReal.ofReal D.degreeBound ≤
            I.sourceHullVolume v R n + ENNReal.ofReal D₀ + (ε : ENNReal) := by
  rintro ⟨D, _⟩
  exact I.not_nonempty_valueHullCompactnessInput_of_degreeFaithful v R n hdeg
    ⟨I.sourceUnitRegionHaarData_to_compactnessInput v R n D⟩

/-- **Conditional assembly of route (i): `unitRegion subset hull` closes
`hunit` with `D0 = 0`.**  With the additional carrier containment
`unitRegion subset hull`, the hunit conclusion holds with `D0 = 0` by
monotonicity of the sup-type volume (`sourceSetVolume_mono`), with no
degree-bound comparison needed (registered route (i) of
`carrier-normalization-crosscheck-20261016.md:107`).  The containment is an
additional hypothesis, not a field of the frozen `SourceUnitRegionHaarData`,
and this conditional form is not the paper's normalization comparison (route
(iii)); it is recorded for the future carrier task, not as progress on route
(iii). -/
theorem cor312GapSupply_sourceInterface_hunit_unitRegion_subset_hull (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (hsub : D.unitRegion ⊆
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))) :
    (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).unitRegion ≤
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
          (I.sourceUnitRegionHaarInterface v R n D).hull +
        ENNReal.ofReal (0 : ℝ) := by
  change I.sourceSetVolume v D.unitRegion ≤
    I.sourceHullVolume v R n + ENNReal.ofReal (0 : ℝ)
  simpa [sourceHullVolume] using I.sourceSetVolume_mono v hsub

end OriginalInput
end Theorem311Source

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the epsilon reshaping of the hunit normalization
obligation: comparison-layer transfer pair, the reshaped obligation and its
consumer drop-in, the satisfiability-space equality, the carrier
unsatisfiability under degree faithfulness, and the conditional assembly of
route (i). -/
def cor312HunitEpsilonTransfer : Obligation :=
  { id := "IUT-III.cor312-hunit-epsilon-transfer"
    source :=
      "IUT III, Corollary 3.12 (log-volume estimates for Theta-pilot objects; " ++
        "holomorphic hull of the union of the possible images, corpus lines " ++
        "10324-10338, 10349-10358); epsilon-absorption pattern of Explicit " ++
        "estimates in IUTeich, Lemma 1.11 (lines 897-903) and Proposition " ++
        "1.12 (lines 906-935)"
    status := VerificationStatus.interface
    note :=
      "Comparison-layer reshaping of the hunit normalization obligation of " ++
        "Cor312ComparisonGapSupplyLayer. PROVED: (T1) the epsilon-to-sharp " ++
        "transfer for ENNReal comparisons and its converse " ++
        "(cor312GapSupply_le_of_forall_pos_le_add, " ++
        "cor312GapSupply_forall_pos_le_add_of_le) -- the reshaping is " ++
        "content-preserving; (T2) the epsilon form of the sharp comparison " ++
        "(cor312GapSupply_hunit_of_epsilon_hullBound), its consumer drop-in " ++
        "(cor312GapSupply_sourceInterface_hunit_of_epsilon_hullBound) and the " ++
        "satisfiability-space equality " ++
        "(cor312GapSupply_exists_epsilon_hullBound_iff_exists_degreeBound_le_hullVolume); " ++
        "(T3) carrier-satisfiability antecedent: under pointwise degree " ++
        "faithfulness the epsilon obligation space is empty " ++
        "(cor312GapSupply_not_exists_epsilon_hullBound_of_degreeFaithful), " ++
        "pinning the frozen refutations SourceHullInterfaceDischarge:232 and " ++
        "IQCarrierConcreteModel:565; (T4) conditional assembly of route (i): " ++
        "unitRegion subset hull gives hunit with D0 = 0 by volume " ++
        "monotonicity (cor312GapSupply_sourceInterface_hunit_unitRegion_subset_hull). " ++
        "NOT proved: the geometric normalization comparison of the paper " ++
        "(degreeBound <= hull volume, route (iii)); the epsilon reshaping adds " ++
        "no geometric content and the value-carrier obligation space stays " ++
        "empty under degree faithfulness."
    dependsOn :=
      [ "IUT-III.cor312-comparison-gap-reduction"
      , "IUT-III.corollary-3.12-iq-hull-interface-discharge"
      , "IUT-III.corollary-3.12-iq-carrier-haar-data"
      , "IUT-III.corollary-3.12-iq-carrier-concrete-model-spike"
      , "IUT-III.corollary-3.12-source-image-hull-volume" ] }

end LeanFormal.IUT.Audit
