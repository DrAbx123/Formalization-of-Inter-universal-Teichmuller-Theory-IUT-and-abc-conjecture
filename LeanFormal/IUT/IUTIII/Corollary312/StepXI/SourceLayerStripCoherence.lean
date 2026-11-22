import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceEvaluationUnitPortionConjugation

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Frozen layer-strip coherence and the agreement of the two conjugation readings

The reduced records carry, for a vertical Kummer arrow, both an `F`-level
representative `stripIso` of the full poly-isomorphism and the Definition
4.9(i) `x`-mu-Kummer layer (Card LK); the reduced record deliberately does not
identify them (`SourceKummerEvaluationArrows.lean`, the `SourceKummerArrow`
docstring).  Accordingly the lower unit portion of the reduced Remark-3.10.2
square admits two readings:

* `SourceEvaluationUnitPortion.ofKummerLayerConjugation` (R2, section 20 of
  `logs/coordination/outsider-survey-transport-20261016.md`): conjugation
  through the two Kummer layers, conditional on the two junction action
  coherences;
* `SourceEvaluationUnitPortion.conjugate` (R3): conjugation along the two
  Kummer strip representatives, as used by the unconditional assembly
  `SourceKummerEvaluationSquare.ofThreeArrows`.

This module freezes the missing coherence as an explicit predicate
(`SourceKummerArrow.LayerStripCoherent`: at every place, the layer's Kummer
equivalence is the descent of the unit-level isomorphism of the `F`-level
representative) and proves that the two readings then agree at the unit-layer
level.  The coherence itself is paper content beyond the frozen records and is
NOT proved here; no inhabitation of the predicate is claimed.  The two
Card-IPL G1 negative results are not re-proved.

## Consumers

The layer-versus-representative coherence bridge listed as residual item 2 of
section 20.4 of the transport report: once a supply line provides the
coherence for the Kummer arrows, R2 and R3 are interchangeable in the SHE
assembly (`SourceSHETransportObligations.sheSupply`, `StepXIContract.she`,
Corollary 3.12, Step (xi-b)).
-/

namespace LeanFormal.IUT

universe uv upi umon uG uU uW

noncomputable section

variable {V : Type uv}

namespace TimesMuQuotient

/-- Descent to the torsion quotient commutes with taking inverses. -/
theorem descent_symm {U : Type uU} {W : Type uW} [CommGroup U] [CommGroup W]
    (e : U ≃* W) :
    descent e.symm = (descent e).symm := by
  ext x
  obtain ⟨u, rfl⟩ := quotientMap_surjective x
  have hA : descent e.symm (quotientMap u) = quotientMap (e.symm u) :=
    descent_quotientMap e.symm u
  have hB : (descent e) (quotientMap (e.symm u)) = quotientMap u := by
    rw [descent_quotientMap, MulEquiv.apply_symm_apply]
  have hC : (descent e).symm (quotientMap u) = quotientMap (e.symm u) := by
    rw [← hB]
    exact (descent e).symm_apply_apply (quotientMap (e.symm u))
  exact hA.trans hC.symm

end TimesMuQuotient

namespace Theorem311Source

/-- The frozen layer-strip coherence for a vertical Kummer arrow: at every
place, the Definition 4.9(i) layer equivalence is the descent of the unit-level
isomorphism induced by the `F`-level representative.  This is the reduced form
of the paper's identification of the supplied Hodge-theater layer with the
layer induced by the poly-isomorphism representative; the frozen record
deliberately leaves it free. -/
def SourceKummerArrow.LayerStripCoherent {G : Type uG} [Group G]
    [TopologicalSpace G] {A B : FPrimeStrip.{umon, uv, upi} V}
    (K : SourceKummerArrow G A B) : Prop :=
  ∀ v : V, (K.layer.kummer v).equiv =
    TimesMuQuotient.descent (Units.mapEquiv (K.stripIso.isoMon v))

/-- Under the layer-strip coherence the two conjugation readings of the lower
unit portion agree at the unit-layer level: the layer conjugation
`ofKummerLayerConjugation` (R2) equals the representative conjugation of
`SourceEvaluationUnitPortion.conjugate` (R3) carried by the arrows' `stripIso`s.
The junction action coherences remain explicit hypotheses. -/
theorem SourceEvaluationUnitPortion.ofKummerLayerConjugation_unitLayer_eq_conjugate
    {G : Type uG} [Group G] [TopologicalSpace G]
    {upperLeft upperRight lowerLeft lowerRight : FPrimeStrip.{umon, uv, upi} V}
    (P : SourceEvaluationUnitPortion G upperLeft upperRight)
    (leftK : SourceKummerArrow G lowerLeft upperLeft)
    (rightK : SourceKummerArrow G lowerRight upperRight)
    (hMid : ∀ v, leftK.layer.targetAction v = P.sourceAction v)
    (hRight : ∀ v, P.targetAction v = rightK.layer.targetAction v)
    (hL : leftK.LayerStripCoherent) (hR : rightK.LayerStripCoherent) :
    ∀ v, (ofKummerLayerConjugation P leftK.layer rightK.layer hMid hRight).unitLayer v =
      (P.conjugate leftK.stripIso.symm rightK.stripIso.symm).unitLayer v := by
  intro v
  change ((leftK.layer.kummer v).equiv.trans (P.unitLayer v)).trans
      ((rightK.layer.kummer v).equiv.symm) =
    (TimesMuQuotient.descent
        (Units.mapEquiv ((leftK.stripIso.symm).isoMon v))).symm.trans
      ((P.unitLayer v).trans
        (TimesMuQuotient.descent
          (Units.mapEquiv ((rightK.stripIso.symm).isoMon v))))
  have hsL : (TimesMuQuotient.descent
        (Units.mapEquiv ((leftK.stripIso.symm).isoMon v))).symm =
      (leftK.layer.kummer v).equiv := by
    have h1 : (leftK.stripIso.symm).isoMon v =
        (leftK.stripIso.isoMon v).symm := rfl
    rw [h1, ← Units.mapEquiv_symm (leftK.stripIso.isoMon v),
      TimesMuQuotient.descent_symm, MulEquiv.symm_symm]
    exact (hL v).symm
  have hsR : TimesMuQuotient.descent
        (Units.mapEquiv ((rightK.stripIso.symm).isoMon v)) =
      (rightK.layer.kummer v).equiv.symm := by
    have h1 : (rightK.stripIso.symm).isoMon v =
        (rightK.stripIso.isoMon v).symm := rfl
    rw [h1, ← Units.mapEquiv_symm (rightK.stripIso.isoMon v),
      TimesMuQuotient.descent_symm]
    exact (congrArg MulEquiv.symm (hR v)).symm
  rw [hsL, hsR]
  ext x
  rfl

end Theorem311Source

end

namespace Audit

/-- Layer-strip coherence bridge: the frozen predicate, and the agreement of
the layer-conjugation and representative-conjugation readings of the lower
Card-EV unit portion under it. -/
def sourceLayerStripCoherence : Obligation :=
  { id := "IUT-III.source-layer-strip-coherence"
    source :=
      "IUT III, Remark 3.10.2 (both readings of the lower horizontal " ++
        "arrows); IUT III, Theorem 3.11, (iii), (c); IUT II, Definition " ++
        "4.9, (i)"
    status := VerificationStatus.interface
    note :=
      "The layer-versus-representative coherence (residual item 2 of " ++
        "section 20.4 of the transport report) is frozen as the predicate " ++
        "SourceKummerArrow.LayerStripCoherent: at every place the " ++
        "Definition 4.9(i) layer equivalence is the descent of the " ++
        "unit-level isomorphism of the F-level representative. Under this " ++
        "coherence (and the two junction action coherences), the layer " ++
        "conjugation ofKummerLayerConjugation and the representative " ++
        "conjugation SourceEvaluationUnitPortion.conjugate agree at the " ++
        "unit-layer level. The coherence itself is NOT proved and no " ++
        "inhabitant of the predicate is constructed; the reduced record " ++
        "deliberately does not identify the layer with the representative. " ++
        "The two Card-IPL G1 negative results are not re-proved."
    dependsOn :=
      [ "IUT-III.source-unit-portion-conjugation",
        "IUT-III.source-SHE-transport-conjugation" ] }

end Audit

end LeanFormal.IUT
