import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceKummerEvaluationSquareExtension
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSHETransportConjugation

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Card-EV unit portion at the lower pair: extraction, conjugation, assembly

This module addresses the residual `G1-SRC-b` of the Card-SHE residual table
(`logs/coordination/outsider-survey-transport-20261016.md`, section 19.4): the
Card-EV unit portion `SourceEvaluationUnitPortion G lowerLeft lowerRight` at
the lower pair of the reduced Remark-3.10.2 square.  Three constructions are
provided.

* Extraction (`SourceEvaluationUnitPortion.ofKummerLayer`): a times-mu Kummer
  layer on the same pair yields a unit portion by dropping the
  invariant-image law; the reduced Card-EV record is exactly the
  equivariance fragment of the reduced Card-LK record.
* Layer conjugation (`SourceEvaluationUnitPortion.ofKummerLayerConjugation`):
  the unit layer is the composite of the two Kummer layer equivalences with
  the upper unit portion; conditional on the two junction action coherences
  (the actions at the junctions are carried by different frozen records).
* Representative conjugation and assembly
  (`SourceKummerEvaluationSquare.ofThreeArrows`): the unconditional reading
  through the existing conjugation engine along the Kummer strip
  representatives.  The lower unit portion is the conjugate of the upper one
  along `leftKummer.stripIso.symm` and `rightKummer.stripIso.symm`, the
  unit-level reading of the instruction that each lower horizontal arrow
  may be constructed by conjugating the corresponding upper horizontal
  arrow by the relevant Kummer isomorphisms (IUT III, Remark 3.10.2).  The
  reduced square is then assembled from the three arrows alone, and its
  nonempty characterization collapses to the one of the three arrows.

## What is and is NOT claimed

* Claimed: the constructions above, the `rfl` projections of the assembled
  square, and the three-arrow nonempty characterization.
* NOT claimed: any source-level construction of the Kummer or evaluation
  arrow bodies (the `G1-SRC-a` condition); the layer-versus-representative
  coherence identifying the two conjugation readings (paper content beyond
  the frozen records); any identification of the two arithmetic holomorphic
  structures (the DSH-F SHE trap).  The two Card-IPL G1 negative results
  are not re-proved.

## Consumer

`Theorem311Source.SourceKummerEvaluationSquare.sheSupply` and `sheLinkSquare`
(`SourceSHETransportObligations.lean`) consume an inhabitant of the reduced
square; `ofThreeArrows u l r` supplies it from the three arrows, with the
lower unit portion derived by the paper's conjugation instruction.
-/

namespace LeanFormal.IUT

universe uv upi umon uG uU uW

noncomputable section

variable {V : Type uv}

namespace TimesMuKummer

namespace Isomorphism

/-- The inverse of a times-mu Kummer isomorphism is equivariant for the
transposed actions: the symmetry companion of the `equivariant` field. -/
theorem symm_equivariant {G : Type uG} [Group G] [TopologicalSpace G]
    {U : Type uU} [CommGroup U] {W : Type uW} [CommGroup W]
    {source : G →* MulAut U} {target : G →* MulAut W}
    (k : Isomorphism source target) (g : G) (x : TimesMuQuotient W) :
    k.equiv.symm (TimesMuQuotient.action target g x) =
      TimesMuQuotient.action source g (k.equiv.symm x) := by
  apply k.equiv.injective
  calc k.equiv (k.equiv.symm (TimesMuQuotient.action target g x))
      = TimesMuQuotient.action target g x :=
        MulEquiv.apply_symm_apply k.equiv _
    _ = TimesMuQuotient.action target g (k.equiv (k.equiv.symm x)) :=
        congrArg (fun z => TimesMuQuotient.action target g z)
          (MulEquiv.apply_symm_apply k.equiv x).symm
    _ = k.equiv (TimesMuQuotient.action source g (k.equiv.symm x)) :=
        (k.equivariant g (k.equiv.symm x)).symm

end Isomorphism

end TimesMuKummer

namespace TimesMuQuotient

/-- Congruence of the descended action in the acting homomorphism. -/
theorem action_congr {G : Type uG} {U : Type uU} [Group G] [CommGroup U]
    {rho rho' : G →* MulAut U} (h : rho = rho') (g : G)
    (x : TimesMuQuotient U) :
    TimesMuQuotient.action rho g x = TimesMuQuotient.action rho' g x :=
  congrArg (fun r => TimesMuQuotient.action r g x) h

end TimesMuQuotient

namespace Theorem311Source

namespace SourceEvaluationUnitPortion

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Extraction of the reduced Card-EV unit portion from a times-mu Kummer
layer on the same pair of strips: take the layer's actions and per-place
Kummer equivalences, dropping the invariant-image law (the paper attaches
that law to Kummer structures, not to the evaluation isomorphism). -/
def ofKummerLayer {upper lower : FPrimeStrip.{umon, uv, upi} V}
    (L : SourceTimesMuKummerLayer G upper lower) :
    SourceEvaluationUnitPortion G upper lower where
  sourceAction := L.sourceAction
  targetAction := L.targetAction
  unitLayer := fun v => (L.kummer v).equiv
  unitLayer_equivariant := fun v g x => (L.kummer v).equivariant g x

/-- Conjugation of an upper unit portion through the two times-mu Kummer
layers at the junctions: the unit layer is the composite of the left layer,
the upper portion, and the inverse of the right layer.  Conditional on the
two junction action coherences, which connect actions carried by different
frozen records. -/
def ofKummerLayerConjugation
    {upperLeft upperRight lowerLeft lowerRight : FPrimeStrip.{umon, uv, upi} V}
    (upperPortion : SourceEvaluationUnitPortion G upperLeft upperRight)
    (leftLayer : SourceTimesMuKummerLayer G lowerLeft upperLeft)
    (rightLayer : SourceTimesMuKummerLayer G lowerRight upperRight)
    (hMid : ∀ v, leftLayer.targetAction v = upperPortion.sourceAction v)
    (hRight : ∀ v, upperPortion.targetAction v = rightLayer.targetAction v) :
    SourceEvaluationUnitPortion G lowerLeft lowerRight where
  sourceAction := leftLayer.sourceAction
  targetAction := rightLayer.sourceAction
  unitLayer := fun v =>
    ((leftLayer.kummer v).equiv.trans (upperPortion.unitLayer v)).trans
      (rightLayer.kummer v).equiv.symm
  unitLayer_equivariant := by
    intro v g x
    calc (rightLayer.kummer v).equiv.symm
          (upperPortion.unitLayer v ((leftLayer.kummer v).equiv
            (TimesMuQuotient.action (leftLayer.sourceAction v) g x)))
        = (rightLayer.kummer v).equiv.symm
          (upperPortion.unitLayer v
            (TimesMuQuotient.action (leftLayer.targetAction v) g
              ((leftLayer.kummer v).equiv x))) :=
          congrArg (fun y => (rightLayer.kummer v).equiv.symm
            (upperPortion.unitLayer v y)) ((leftLayer.kummer v).equivariant g x)
      _ = (rightLayer.kummer v).equiv.symm
          (upperPortion.unitLayer v
            (TimesMuQuotient.action (upperPortion.sourceAction v) g
              ((leftLayer.kummer v).equiv x))) :=
          congrArg (fun y => (rightLayer.kummer v).equiv.symm
            (upperPortion.unitLayer v y))
            (TimesMuQuotient.action_congr (hMid v) g
              ((leftLayer.kummer v).equiv x))
      _ = (rightLayer.kummer v).equiv.symm
          (TimesMuQuotient.action (upperPortion.targetAction v) g
            (upperPortion.unitLayer v ((leftLayer.kummer v).equiv x))) :=
          congrArg (rightLayer.kummer v).equiv.symm
            (upperPortion.unitLayer_equivariant v g
              ((leftLayer.kummer v).equiv x))
      _ = (rightLayer.kummer v).equiv.symm
          (TimesMuQuotient.action (rightLayer.targetAction v) g
            (upperPortion.unitLayer v ((leftLayer.kummer v).equiv x))) :=
          congrArg (rightLayer.kummer v).equiv.symm
            (TimesMuQuotient.action_congr (hRight v) g
              (upperPortion.unitLayer v ((leftLayer.kummer v).equiv x)))
      _ = TimesMuQuotient.action (rightLayer.sourceAction v) g
          ((rightLayer.kummer v).equiv.symm
            (upperPortion.unitLayer v ((leftLayer.kummer v).equiv x))) :=
          TimesMuKummer.Isomorphism.symm_equivariant (rightLayer.kummer v) g
            (upperPortion.unitLayer v ((leftLayer.kummer v).equiv x))
      _ = TimesMuQuotient.action (rightLayer.sourceAction v) g
          (((leftLayer.kummer v).equiv.trans (upperPortion.unitLayer v)).trans
            (rightLayer.kummer v).equiv.symm x) := rfl

end SourceEvaluationUnitPortion

namespace SourceKummerEvaluationSquare

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {upperLeft upperRight lowerLeft lowerRight :
  FPrimeStrip.{umon, uv, upi} V}

/-- The reduced square assembled from three arrows, with the lower unit
portion derived by conjugation: the unit-level reading of the
Remark-3.10.2 instruction that each lower horizontal arrow may be
constructed by conjugating the corresponding upper horizontal arrow by the
relevant Kummer isomorphisms.  The lower unit portion is the conjugate of
the upper one along the two Kummer strip representatives, matching the
strip-level conjugation formula frozen by `ofThreeLegs`. -/
def ofThreeArrows
    (upperHorizontal : SourceEvaluationArrow G upperLeft upperRight)
    (leftKummer : SourceKummerArrow G lowerLeft upperLeft)
    (rightKummer : SourceKummerArrow G lowerRight upperRight) :
    SourceKummerEvaluationSquare G upperLeft upperRight lowerLeft lowerRight :=
  ofThreeLegs upperHorizontal leftKummer rightKummer
    (upperHorizontal.unitPortion.conjugate leftKummer.stripIso.symm
      rightKummer.stripIso.symm)

@[simp] theorem ofThreeArrows_upperHorizontal
    (upperHorizontal : SourceEvaluationArrow G upperLeft upperRight)
    (leftKummer : SourceKummerArrow G lowerLeft upperLeft)
    (rightKummer : SourceKummerArrow G lowerRight upperRight) :
    (ofThreeArrows upperHorizontal leftKummer rightKummer).upperHorizontal =
      upperHorizontal := rfl

@[simp] theorem ofThreeArrows_leftKummer
    (upperHorizontal : SourceEvaluationArrow G upperLeft upperRight)
    (leftKummer : SourceKummerArrow G lowerLeft upperLeft)
    (rightKummer : SourceKummerArrow G lowerRight upperRight) :
    (ofThreeArrows upperHorizontal leftKummer rightKummer).leftKummer =
      leftKummer := rfl

@[simp] theorem ofThreeArrows_rightKummer
    (upperHorizontal : SourceEvaluationArrow G upperLeft upperRight)
    (leftKummer : SourceKummerArrow G lowerLeft upperLeft)
    (rightKummer : SourceKummerArrow G lowerRight upperRight) :
    (ofThreeArrows upperHorizontal leftKummer rightKummer).rightKummer =
      rightKummer := rfl

@[simp] theorem ofThreeArrows_lowerHorizontal_stripIso
    (upperHorizontal : SourceEvaluationArrow G upperLeft upperRight)
    (leftKummer : SourceKummerArrow G lowerLeft upperLeft)
    (rightKummer : SourceKummerArrow G lowerRight upperRight) :
    (ofThreeArrows upperHorizontal leftKummer
      rightKummer).lowerHorizontal.stripIso =
      leftKummer.stripIso.trans
        (upperHorizontal.stripIso.trans rightKummer.stripIso.symm) := rfl

@[simp] theorem ofThreeArrows_lowerHorizontal_unitPortion
    (upperHorizontal : SourceEvaluationArrow G upperLeft upperRight)
    (leftKummer : SourceKummerArrow G lowerLeft upperLeft)
    (rightKummer : SourceKummerArrow G lowerRight upperRight) :
    (ofThreeArrows upperHorizontal leftKummer
      rightKummer).lowerHorizontal.unitPortion =
      upperHorizontal.unitPortion.conjugate leftKummer.stripIso.symm
        rightKummer.stripIso.symm := rfl

/-- The three-arrow inhabitation characterization: a reduced square exists
exactly when the upper evaluation arrow and the two Kummer arrows exist.
The lower unit portion is supplied by the conjugation construction
(`ofThreeArrows`), so it is no longer a free input of the reduced record. -/
theorem sourceKummerEvaluationSquare_nonempty_iff_threeArrows :
    Nonempty (SourceKummerEvaluationSquare G upperLeft upperRight lowerLeft lowerRight) ↔
      Nonempty (SourceEvaluationArrow G upperLeft upperRight) ∧
        Nonempty (SourceKummerArrow G lowerLeft upperLeft) ∧
        Nonempty (SourceKummerArrow G lowerRight upperRight) :=
  ⟨fun ⟨S⟩ => ⟨⟨S.upperHorizontal⟩, ⟨S.leftKummer⟩, ⟨S.rightKummer⟩⟩,
    fun ⟨⟨u⟩, ⟨l⟩, ⟨r⟩⟩ => ⟨ofThreeArrows u l r⟩⟩

end SourceKummerEvaluationSquare

end Theorem311Source

end

namespace Audit

/-- Card-EV unit portion at the lower pair: extraction, layer conjugation,
and the unconditional representative conjugation with square assembly. -/
def sourceUnitPortionConjugation : Obligation :=
  { id := "IUT-III.source-unit-portion-conjugation"
    source :=
      "IUT III, Remark 3.10.2 (conjugation of the lower horizontal arrows); " ++
        "IUT II, Corollary 4.10, (ii) (Card EV); Corollary 3.12, proof, " ++
        "Step (xi-b)"
    status := VerificationStatus.interface
    note :=
      "The residual G1-SRC-b (the lower-pair Card-EV unit portion) is " ++
        "constructed, not postulated: extraction from a same-pair times-mu " ++
        "Kummer layer (dropping the invariant-image law); conjugation " ++
        "through the two Kummer layers conditional on the two junction " ++
        "action coherences; and the unconditional representative " ++
        "conjugation along the Kummer strip representatives, with the " ++
        "assembly SourceKummerEvaluationSquare.ofThreeArrows. The reduced " ++
        "square is thereby inhabited from the three arrows alone, and its " ++
        "nonempty characterization collapses to the nonempty " ++
        "characterization of the three arrows. NOT constructed: the " ++
        "source-level arrow bodies (G1-SRC-a). NOT proved: the " ++
        "layer-versus-representative coherence identifying the two " ++
        "conjugation readings. The two Card-IPL G1 negative results are " ++
        "not re-proved."
    dependsOn :=
      [ "IUT-III.source-kummer-evaluation-square-extension",
        "IUT-III.source-SHE-transport-conjugation",
        "IUT-III.source-kummer-evaluation-arrows" ] }

end Audit

end LeanFormal.IUT
