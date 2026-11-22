import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSHETransportObligations

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Card-SHE transport by conjugation: the times-mu upgrade records

This module supplies the transport-version content of the Card-SHE
conditional assembly: the per-leg upgrade records of
`SourceSHETransportObligations.lean` (evaluation-arrow and Kummer-arrow
records carrying the times-mu data) are transported along equivalences of
the corner strips, and the whole `SourceSHESquareSupply` is transported
coherently with the link-conjugation engine and the square transport of
`SourceSHETransportLaws.lean` (the Remark 3.10.2 conjugation square).

What is built:

1. conjugation of an `FPrimeStripEquiv` representative together with the
   coherence of the `toLink` bridge (`toLink_conjugate`,
   `toLink_conjugate_symm`): the underlying link of a conjugated
   representative is the conjugate of the underlying link;
2. transport of the times-mu layer: descent of multiplicative equivalences
   to the torsion quotient `TimesMuQuotient`
   (`TimesMuQuotient.descent`), conjugation of `G`-actions
   (`TimesMuKummer.actionConj`), equivariance of the descent
   (`TimesMuQuotient.descent_action`, `TimesMuQuotient.descent_conj_equivariant`),
   transport of the invariant-image subgroups
   (`TimesMuKummer.descent_image_invariantImage`), and conjugation of
   `TimesMuKummer.Isomorphism` (equivariance and invariant-image law);
3. conjugation of the layer and portion records
   (`Theorem311Source.SourceTimesMuKummerLayer.conjugate`,
   `Theorem311Source.SourceEvaluationUnitPortion.conjugate`), of the two arrow records
   (`Theorem311Source.SourceKummerArrow.conjugate`,
   `Theorem311Source.SourceEvaluationArrow.conjugate`), and of the four
   per-leg upgrade records;
4. the transported supply `SourceSHESquareSupply.conjugate` with its field
   laws, definitionally coherent with
   `SourceSimultaneousHolomorphicExpression.transport` of the module
   `SourceSHETransportLaws.lean`.

Paper location: IUT III, Remark 3.10.2 (the conjugation square); Remark
3.11.1, (iii) (SHE); Corollary 3.12, proof, Step (xi-b).

Non-claims: this is transport of the frozen conditional records only; it
constructs no source Kummer or evaluation arrow (the S2/G1 source
obligation remains the explicit condition of the supply), and it does not
reprove the two Card-IPL G1 negative results.  Every transport theorem is
conditional on its input record.
-/

namespace LeanFormal.IUT

universe uv upi umon uG uU uW

variable {V : Type uv}

/-! ## 1. Conjugation of representatives and the toLink bridge -/

namespace FPrimeStripEquiv

/-- Conjugate an equivalence representative along equivalences of its two
strips: read the source through `sigma` and the target through `tau`. -/
def conjugate {A A' B B' : FPrimeStrip.{umon, uv, upi} V}
    (e : FPrimeStripEquiv A B) (sigma : FPrimeStripEquiv A A')
    (tau : FPrimeStripEquiv B B') : FPrimeStripEquiv A' B' :=
  sigma.symm.trans (e.trans tau)

/-- Coherence of the link bridge with conjugation: the underlying link of a
conjugated representative is the conjugated underlying link. -/
theorem toLink_conjugate {A A' B B' : FPrimeStrip.{umon, uv, upi} V}
    (e : FPrimeStripEquiv A B) (sigma : FPrimeStripEquiv A A')
    (tau : FPrimeStripEquiv B B') :
    (e.conjugate sigma tau).toLink = e.toLink.conjugate sigma tau := by
  rfl

/-- The same coherence for the inverse representative, in the shape used by
the reverse-direction (stored) records of Remark 3.10.2. -/
theorem toLink_conjugate_symm {A A' B B' : FPrimeStrip.{umon, uv, upi} V}
    (e : FPrimeStripEquiv A B) (sigma : FPrimeStripEquiv A A')
    (tau : FPrimeStripEquiv B B') :
    ((e.conjugate sigma tau).symm).toLink =
      (e.symm).toLink.conjugate tau sigma := by
  rfl

end FPrimeStripEquiv

/-! ## 2. The times-mu transport engine -/

namespace MulAut

/-- Conjugation of automorphism groups along a multiplicative equivalence:
`f` is sent to `e * f * e^{-1}`. -/
noncomputable def conjEquiv {U : Type uU} {W : Type uW} [Group U] [Group W]
    (e : U ≃* W) : MulAut U ≃* MulAut W where
  toFun f := (e.symm.trans f).trans e
  invFun f := (e.trans f).trans e.symm
  left_inv f := by
    ext x
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  right_inv f := by
    ext x
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  map_mul' f g := by
    ext x
    simp only [MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

end MulAut

namespace TimesMuKummer

/-- Conjugation of `G`-actions along a multiplicative equivalence. -/
noncomputable def actionConj {G : Type uG} {U : Type uU} {W : Type uW}
    [Group G] [Group U] [Group W] (e : U ≃* W) (rho : G →* MulAut U) :
    G →* MulAut W :=
  (MulAut.conjEquiv e).toMonoidHom.comp rho

/-- Pointwise evaluation of a conjugated action. -/
@[simp] theorem actionConj_apply {G : Type uG} {U : Type uU} {W : Type uW}
    [Group G] [Group U] [Group W] (e : U ≃* W) (rho : G →* MulAut U)
    (g : G) (w : W) :
    (actionConj e rho) g w = e (rho g (e.symm w)) := rfl

end TimesMuKummer

namespace TimesMuQuotient

/-- Descent of a multiplicative equivalence to the quotient by torsion. -/
noncomputable def descent {U : Type uU} {W : Type uW} [CommGroup U] [CommGroup W]
    (e : U ≃* W) : TimesMuQuotient U ≃* TimesMuQuotient W :=
  QuotientGroup.congr (CommGroup.torsion U) (CommGroup.torsion W) e e.map_torsion

@[simp] theorem descent_quotientMap {U : Type uU} {W : Type uW}
    [CommGroup U] [CommGroup W] (e : U ≃* W) (u : U) :
    descent e (quotientMap u) = quotientMap (e u) :=
  QuotientGroup.congr_mk (G' := CommGroup.torsion U)
    (H' := CommGroup.torsion W) e e.map_torsion u

/-- Descent is equivariant for a conjugated action. -/
theorem descent_action {G : Type uG} {U : Type uU} {W : Type uW}
    [Group G] [CommGroup U] [CommGroup W]
    (e : U ≃* W) (rho : G →* MulAut U) (g : G) (x : TimesMuQuotient U) :
    descent e (action rho g x) =
      action (TimesMuKummer.actionConj e rho) g (descent e x) := by
  obtain ⟨u, rfl⟩ := quotientMap_surjective x
  simp only [action_quotientMap, descent_quotientMap, TimesMuKummer.actionConj_apply,
    MulEquiv.symm_apply_apply]

/-- Equivariance transport: the conjugate of an equivariant equivalence is
equivariant for the conjugated actions. -/
theorem descent_conj_equivariant {G : Type uG} {U U' : Type uU} {W W' : Type uW}
    [Group G] [CommGroup U] [CommGroup U'] [CommGroup W] [CommGroup W']
    (eu : U ≃* U') (ew : W ≃* W') (source : G →* MulAut U)
    (target : G →* MulAut W) (lam : TimesMuQuotient U ≃* TimesMuQuotient W)
    (hlam : ∀ g x, lam (action source g x) = action target g (lam x)) :
    ∀ g x, ((descent eu).symm.trans (lam.trans (descent ew)))
        (action (TimesMuKummer.actionConj eu source) g x) =
      action (TimesMuKummer.actionConj ew target) g
        (((descent eu).symm.trans (lam.trans (descent ew))) x) := by
  intro g x
  obtain ⟨x0, rfl⟩ := (descent eu).surjective x
  have h1 : ((descent eu).symm.trans (lam.trans (descent ew)))
      (action (TimesMuKummer.actionConj eu source) g (descent eu x0)) =
      descent ew (lam (action source g x0)) := by
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply,
      ← descent_action eu source g x0, MulEquiv.symm_apply_apply]
  have h2 : ((descent eu).symm.trans (lam.trans (descent ew))) (descent eu x0) =
      descent ew (lam x0) := by
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [h1, h2, hlam g x0]
  exact descent_action ew target g (lam x0)

end TimesMuQuotient

namespace TimesMuKummer

/-- Transport of the invariant-image subgroups along the descent: the descent
of the invariants is the invariants of the conjugated action. -/
theorem descent_image_invariantImage {G : Type uG} {U U' : Type uU}
    [Group G] [TopologicalSpace G] [CommGroup U] [CommGroup U']
    (e : U ≃* U') (rho : G →* MulAut U) (H : OpenSubgroup G) :
    TimesMuQuotient.descent e ''
        (invariantImage rho H : Set (TimesMuQuotient U)) =
      (invariantImage (actionConj e rho) H : Set (TimesMuQuotient U')) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ := (mem_invariantImage_iff rho H y).mp hy
    refine (mem_invariantImage_iff (actionConj e rho) H _).mpr
      ⟨e u, fun g => ?_, (TimesMuQuotient.descent_quotientMap e u).symm⟩
    have hpu : (actionConj e rho) (g : G) (e u) = e (rho (g : G) u) := by
      rw [actionConj_apply, MulEquiv.symm_apply_apply]
    rw [hpu, hu g]
  · intro hx
    obtain ⟨u', hu', rfl⟩ := (mem_invariantImage_iff (actionConj e rho) H x).mp hx
    refine ⟨TimesMuQuotient.quotientMap (e.symm u'), ?_, ?_⟩
    · refine (mem_invariantImage_iff rho H _).mpr ⟨e.symm u', fun g => ?_, rfl⟩
      have hg := hu' g
      have hred : (actionConj e rho) (g : G) u' = e (rho (g : G) (e.symm u')) :=
        actionConj_apply e rho (g : G) u'
      rw [hred] at hg
      exact e.injective (by rw [hg, MulEquiv.apply_symm_apply])
    · rw [TimesMuQuotient.descent_quotientMap, MulEquiv.apply_symm_apply]

namespace Isomorphism

/-- Conjugation of a times-mu Kummer isomorphism along multiplicative
equivalences of its source and target carriers. -/
noncomputable def conjugate {G : Type uG} {U U' : Type uU} {W W' : Type uW}
    [Group G] [TopologicalSpace G] [CommGroup U] [CommGroup U'] [CommGroup W] [CommGroup W']
    {source : G →* MulAut U} {target : G →* MulAut W}
    (iso : TimesMuKummer.Isomorphism source target) (eu : U ≃* U')
    (ew : W ≃* W') :
    TimesMuKummer.Isomorphism (actionConj eu source) (actionConj ew target) where
  equiv := (TimesMuQuotient.descent eu).symm.trans
    (iso.equiv.trans (TimesMuQuotient.descent ew))
  equivariant := TimesMuQuotient.descent_conj_equivariant eu ew source target
    iso.equiv iso.equivariant
  invariantImage := by
    intro H
    calc
      ((TimesMuQuotient.descent eu).symm.trans
          (iso.equiv.trans (TimesMuQuotient.descent ew))) ''
          (TimesMuKummer.invariantImage (actionConj eu source) H :
            Set (TimesMuQuotient U')) =
        TimesMuQuotient.descent ew '' (iso.equiv ''
          ((TimesMuQuotient.descent eu).symm ''
            (TimesMuKummer.invariantImage (actionConj eu source) H :
              Set (TimesMuQuotient U')))) := by
          simp only [MulEquiv.coe_trans, Set.image_comp]
      _ = TimesMuQuotient.descent ew '' (iso.equiv ''
          (TimesMuKummer.invariantImage source H : Set (TimesMuQuotient U))) := by
          rw [← TimesMuKummer.descent_image_invariantImage eu source H]
          refine congrArg (fun t : Set (TimesMuQuotient U) =>
            TimesMuQuotient.descent ew '' (iso.equiv '' t)) ?_
          ext x
          constructor
          · rintro ⟨y, hy, hxy⟩
            obtain ⟨z, hz, hyz⟩ := hy
            rw [← hyz, MulEquiv.symm_apply_apply] at hxy
            exact hxy ▸ hz
          · rintro hx
            exact ⟨(TimesMuQuotient.descent eu) x, ⟨x, hx, rfl⟩,
              MulEquiv.symm_apply_apply (TimesMuQuotient.descent eu) x⟩
      _ = TimesMuQuotient.descent ew ''
          (TimesMuKummer.invariantImage target H : Set (TimesMuQuotient W)) := by
          rw [iso.invariantImage H]
      _ = (TimesMuKummer.invariantImage (actionConj ew target) H :
          Set (TimesMuQuotient W')) :=
          TimesMuKummer.descent_image_invariantImage ew target H

end Isomorphism

end TimesMuKummer

/-! ## 3. Transport of the layer, portion, and arrow records -/

namespace Theorem311Source

namespace SourceTimesMuKummerLayer

/-- Conjugation of a reduced times-mu Kummer layer along strip equivalences:
the actions are conjugated and the per-place Kummer isomorphisms are
transported. -/
noncomputable def conjugate {G : Type uG} [Group G] [TopologicalSpace G]
    {upper upper' lower lower' : FPrimeStrip.{umon, uv, upi} V}
    (L : SourceTimesMuKummerLayer G upper lower)
    (sigma : FPrimeStripEquiv upper upper')
    (tau : FPrimeStripEquiv lower lower') :
    SourceTimesMuKummerLayer G upper' lower' where
  sourceAction := fun v =>
    TimesMuKummer.actionConj (Units.mapEquiv (sigma.isoMon v)) (L.sourceAction v)
  targetAction := fun v =>
    TimesMuKummer.actionConj (Units.mapEquiv (tau.isoMon v)) (L.targetAction v)
  kummer := fun v =>
    TimesMuKummer.Isomorphism.conjugate (L.kummer v)
      (Units.mapEquiv (sigma.isoMon v)) (Units.mapEquiv (tau.isoMon v))

end SourceTimesMuKummerLayer

namespace SourceEvaluationUnitPortion

/-- Conjugation of the Card-EV unit portion along strip equivalences. -/
noncomputable def conjugate {G : Type uG} [Group G] [TopologicalSpace G]
    {upper upper' lower lower' : FPrimeStrip.{umon, uv, upi} V}
    (P : SourceEvaluationUnitPortion G upper lower)
    (sigma : FPrimeStripEquiv upper upper')
    (tau : FPrimeStripEquiv lower lower') :
    SourceEvaluationUnitPortion G upper' lower' where
  sourceAction := fun v =>
    TimesMuKummer.actionConj (Units.mapEquiv (sigma.isoMon v)) (P.sourceAction v)
  targetAction := fun v =>
    TimesMuKummer.actionConj (Units.mapEquiv (tau.isoMon v)) (P.targetAction v)
  unitLayer := fun v =>
    (TimesMuQuotient.descent (Units.mapEquiv (sigma.isoMon v))).symm.trans
      ((P.unitLayer v).trans (TimesMuQuotient.descent (Units.mapEquiv (tau.isoMon v))))
  unitLayer_equivariant := fun v =>
    TimesMuQuotient.descent_conj_equivariant (Units.mapEquiv (sigma.isoMon v))
      (Units.mapEquiv (tau.isoMon v)) (P.sourceAction v) (P.targetAction v)
      (P.unitLayer v) (P.unitLayer_equivariant v)

end SourceEvaluationUnitPortion

namespace SourceKummerArrow

/-- Conjugation of a source-level Kummer arrow along strip equivalences. -/
noncomputable def conjugate {G : Type uG} [Group G] [TopologicalSpace G]
    {A A' B B' : FPrimeStrip.{umon, uv, upi} V} (K : SourceKummerArrow G A B)
    (sigma : FPrimeStripEquiv A A') (tau : FPrimeStripEquiv B B') :
    SourceKummerArrow G A' B' where
  stripIso := K.stripIso.conjugate sigma tau
  layer := K.layer.conjugate sigma tau

end SourceKummerArrow

namespace SourceEvaluationArrow

/-- Conjugation of a source-level evaluation arrow along strip equivalences. -/
noncomputable def conjugate {G : Type uG} [Group G] [TopologicalSpace G]
    {A A' B B' : FPrimeStrip.{umon, uv, upi} V} (E : SourceEvaluationArrow G A B)
    (sigma : FPrimeStripEquiv A A') (tau : FPrimeStripEquiv B B') :
    SourceEvaluationArrow G A' B' where
  stripIso := E.stripIso.conjugate sigma tau
  unitPortion := E.unitPortion.conjugate sigma tau

end SourceEvaluationArrow

end Theorem311Source

/-! ## 4. Transport of the per-leg upgrade records and of the supply -/

namespace SourceEvaluationLegUpgrade

/-- Conjugation of an evaluation-leg upgrade record: the transported arrow has
the conjugated representative, and the leg equation transports. -/
noncomputable def conjugate {G : Type uG} [Group G] [TopologicalSpace G]
    {A A' B B' : FPrimeStrip.{umon, uv, upi} V} {leg : FPrimeStripLink A B}
    (U : SourceEvaluationLegUpgrade G leg) (sigma : FPrimeStripEquiv A A')
    (tau : FPrimeStripEquiv B B') :
    SourceEvaluationLegUpgrade G (leg.conjugate sigma tau) where
  arrow := U.arrow.conjugate sigma tau
  leg_eq := by
    change (U.arrow.stripIso.conjugate sigma tau).toLink = leg.conjugate sigma tau
    rw [FPrimeStripEquiv.toLink_conjugate, U.leg_eq]

end SourceEvaluationLegUpgrade

namespace SourceKummerLegUpgrade

/-- Conjugation of a Kummer-leg upgrade record (forward direction). -/
noncomputable def conjugate {G : Type uG} [Group G] [TopologicalSpace G]
    {A A' B B' : FPrimeStrip.{umon, uv, upi} V} {leg : FPrimeStripLink A B}
    (U : SourceKummerLegUpgrade G leg) (sigma : FPrimeStripEquiv A A')
    (tau : FPrimeStripEquiv B B') :
    SourceKummerLegUpgrade G (leg.conjugate sigma tau) where
  arrow := U.arrow.conjugate sigma tau
  leg_eq := by
    change (U.arrow.stripIso.conjugate sigma tau).toLink = leg.conjugate sigma tau
    rw [FPrimeStripEquiv.toLink_conjugate, U.leg_eq]

end SourceKummerLegUpgrade

namespace SourceReverseKummerLegUpgrade

/-- Conjugation of a Kummer-leg upgrade record in the reverse (stored)
direction of Remark 3.10.2. -/
noncomputable def conjugate {G : Type uG} [Group G] [TopologicalSpace G]
    {A A' C C' : FPrimeStrip.{umon, uv, upi} V} {leg : FPrimeStripLink A C}
    (U : SourceReverseKummerLegUpgrade G leg) (sigma : FPrimeStripEquiv A A')
    (tau : FPrimeStripEquiv C C') :
    SourceReverseKummerLegUpgrade G (leg.conjugate sigma tau) where
  arrow := U.arrow.conjugate tau sigma
  leg_eq := by
    change ((U.arrow.stripIso.conjugate tau sigma).symm).toLink =
      leg.conjugate sigma tau
    rw [FPrimeStripEquiv.toLink_conjugate_symm, U.leg_eq]

end SourceReverseKummerLegUpgrade

namespace SourceSHESquareSupply

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {A A' B B' C C' D D' : FPrimeStrip.{umon, uv, upi} V}

/-- Transport the whole conditional supply along a quadruple of strip
equivalences: every leg and both expressions are conjugated, the square is
the transported simultaneity square of `SourceSHETransportLaws`, and the
four upgrade records are conjugated. -/
noncomputable def conjugate (W : SourceSHESquareSupply G A B C D)
    (sigmaA : FPrimeStripEquiv A A') (sigmaB : FPrimeStripEquiv B B')
    (sigmaC : FPrimeStripEquiv C C') (sigmaD : FPrimeStripEquiv D D') :
    SourceSHESquareSupply G A' B' C' D' where
  upperHorizontalLeg := W.upperHorizontalLeg.conjugate sigmaA sigmaB
  lowerHorizontalLeg := W.lowerHorizontalLeg.conjugate sigmaC sigmaD
  leftKummerLeg := W.leftKummerLeg.conjugate sigmaA sigmaC
  rightKummerLeg := W.rightKummerLeg.conjugate sigmaB sigmaD
  square := W.square.transport sigmaA sigmaB sigmaC sigmaD
  upperHorizontalUpgrade := W.upperHorizontalUpgrade.conjugate sigmaA sigmaB
  lowerHorizontalUpgrade := W.lowerHorizontalUpgrade.conjugate sigmaC sigmaD
  leftKummerUpgrade := W.leftKummerUpgrade.conjugate sigmaA sigmaC
  rightKummerUpgrade := W.rightKummerUpgrade.conjugate sigmaB sigmaD

@[simp] theorem conjugate_square (W : SourceSHESquareSupply G A B C D)
    (sigmaA : FPrimeStripEquiv A A') (sigmaB : FPrimeStripEquiv B B')
    (sigmaC : FPrimeStripEquiv C C') (sigmaD : FPrimeStripEquiv D D') :
    (W.conjugate sigmaA sigmaB sigmaC sigmaD).square =
      W.square.transport sigmaA sigmaB sigmaC sigmaD := rfl

@[simp] theorem conjugate_upperHorizontalLeg (W : SourceSHESquareSupply G A B C D)
    (sigmaA : FPrimeStripEquiv A A') (sigmaB : FPrimeStripEquiv B B')
    (sigmaC : FPrimeStripEquiv C C') (sigmaD : FPrimeStripEquiv D D') :
    (W.conjugate sigmaA sigmaB sigmaC sigmaD).upperHorizontalLeg =
      W.upperHorizontalLeg.conjugate sigmaA sigmaB := rfl

@[simp] theorem conjugate_lowerHorizontalLeg (W : SourceSHESquareSupply G A B C D)
    (sigmaA : FPrimeStripEquiv A A') (sigmaB : FPrimeStripEquiv B B')
    (sigmaC : FPrimeStripEquiv C C') (sigmaD : FPrimeStripEquiv D D') :
    (W.conjugate sigmaA sigmaB sigmaC sigmaD).lowerHorizontalLeg =
      W.lowerHorizontalLeg.conjugate sigmaC sigmaD := rfl

@[simp] theorem conjugate_leftKummerLeg (W : SourceSHESquareSupply G A B C D)
    (sigmaA : FPrimeStripEquiv A A') (sigmaB : FPrimeStripEquiv B B')
    (sigmaC : FPrimeStripEquiv C C') (sigmaD : FPrimeStripEquiv D D') :
    (W.conjugate sigmaA sigmaB sigmaC sigmaD).leftKummerLeg =
      W.leftKummerLeg.conjugate sigmaA sigmaC := rfl

@[simp] theorem conjugate_rightKummerLeg (W : SourceSHESquareSupply G A B C D)
    (sigmaA : FPrimeStripEquiv A A') (sigmaB : FPrimeStripEquiv B B')
    (sigmaC : FPrimeStripEquiv C C') (sigmaD : FPrimeStripEquiv D D') :
    (W.conjugate sigmaA sigmaB sigmaC sigmaD).rightKummerLeg =
      W.rightKummerLeg.conjugate sigmaB sigmaD := rfl

end SourceSHESquareSupply

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Card-SHE transport by conjugation: the times-mu upgrade records and the
whole conditional supply transport along strip equivalences. -/
def sourceSHETransportConjugation : Obligation :=
  { id := "IUT-III.source-SHE-transport-conjugation"
    source :=
      "IUT III, Remark 3.10.2 (conjugation square); Remark 3.11.1, (iii) " ++
        "(SHE); Corollary 3.12, proof, Step (xi-b)"
    status := VerificationStatus.interface
    note :=
      "Transport of the Card-SHE conditional assembly along strip " ++
        "equivalences: representative conjugation with toLink coherence; " ++
        "times-mu transport (torsion-quotient descent, action conjugation, " ++
        "equivariance transport, invariant-image transport, Kummer-isomorphism " ++
        "conjugation); conjugation of the layer, portion, arrow, and per-leg " ++
        "upgrade records; and the transported supply SourceSHESquareSupply.conjugate " ++
        "coherent with SourceSimultaneousHolomorphicExpression.transport. The " ++
        "transport of the times-mu layer is constructed, not postulated; the " ++
        "source-level inhabitants remain the open S2/G1 obligation of the supply " ++
        "condition. No slot is closed by True; the two Card-IPL G1 negative " ++
        "results are not re-proved."
    dependsOn :=
      [ "IUT-III.source-SHE-simultaneity-exchange",
        "IUT-III.source-SHE-obligations",
        "IUT-III.source-kummer-evaluation-arrows",
        "IUT-I-II.prime-strip-core" ] }

end LeanFormal.IUT.Audit
