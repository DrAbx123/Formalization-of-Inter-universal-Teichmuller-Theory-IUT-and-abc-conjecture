import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierConcreteModel
import LeanFormal.IUT.ABCBridge.Bridge.Cor312CarrierRealizationSpec

/-!
# d5-e2 alignment: the concrete carrier model against the frozen Cor 3.12 carrier spec

Task N9.  Companions (imported; no existing file is modified):

* `IQCarrierConcreteModel.lean` (task d5): the concrete real-line carrier model
  with the five reduced inputs, the weight dictionary
  `iqCarrierModel_weightDictionary` (its own shell point map), the separate-map
  point-height dictionary `iqCarrierModel_pointHeightDictionary`, the two hunit
  shapes, and the single-map refutation
  `iqCarrierModel_valueCarrier_no_jointDictionaries`.
* `Cor312CarrierRealizationSpec.lean` (task e2): the frozen four-field package
  `Cor312CarrierRealizationSpec`, its two assembly defs
  (`cor312CarrierSpec_epsilonComparison_of_dictionaries`,
  `cor312CarrierSpec_epsilonComparison`), and the package refutation
  `cor312CarrierSpec_not_inhabited`.

## Alignment verdict

1. **Full instantiation of the frozen combined def is impossible, and that
   impossibility is proved here** (`iqCarrierAlignment_jointDictionaries_refuted`).
   The combined def consumes the weight dictionary and the point-height
   dictionary *at one and the same point map and scaling*; that pair is refuted
   pointwise on every value-realized carrier datum, because at the ABC triple
   `(1, 2, 3)` the two chained inequalities would force `log 6 <= log 3`.  The
   model's dictionaries live on two separated point maps
   (`iqCarrierModelLogShellPoint` for the weight side, `iqCarrierModelPointHeight`
   for the height side) and were never jointly available; no carrier datum can
   repair this, since the refutation is arithmetic, not carrier-internal.  The
   model-side refutation also re-derives the spec-side package refutation through
   its own route: `iqCarrierAlignment_specPackage_refuted` (cross-implementation
   agreement; not a new mathematical fact).

2. **The supplyable reduction, labeled as a reduced form**
   (`iqCarrierAlignment_epsilonComparison_of_weightDictionary_and_volumeCard`):
   the constructive sibling of the frozen combined def in which the point-height
   dictionary is replaced by the direct one-sided point-volume card
   `(vol {lam * p abc}).toReal <= (1 + eps) * weight + D1` -- the shape recorded
   in the e2 judge table and realized at the calibration model as
   `iqCarrierModel_hpoint` (with `D1 = 0`).  All other slots (canonical hunit
   constant, supply-layer weight comparison, unconditional hsplit/hptfin) are
   discharged by the frozen reductions exactly as in the frozen def.  The frozen
   defs and files are untouched; whether to adopt the replacement shape is the
   pending task-level decision, so this def is a reduced form and does not
   replace any frozen statement.

## Paper anchors (field-source judgment)

* IUT III, Corollary 3.12 (statement, pp. 173-174; proof Steps (i)-(xi),
  pp. 175-190): `-|log(Theta)| >= -|log(q)|`, a one-sided comparison of the
  log-volume of the holomorphic hull of the Theta-pilot possible images with the
  q-pilot log-volume.  No two-sided pin of one quantity between an arithmetic
  weight and a height occurs there; the refuted dictionary pair has no paper
  counterpart.
* IUT IV, Theorem A (pp. 2-3): `ht <= (1 + eps)(log-diff + log-cond)` with a
  bounded discrepancy -- the one-sided (1 + eps) shape with an additive constant,
  which is exactly the shape of the volume card used in the reduced form here.
* IUT IV, section 2 (pp. 40-41): the notation review (log-diff, log-cond,
  ht) in which the final inequality is stated.

Text locations for the citations above: `papers/motizuki_corpus/text/
Inter-universal Teichmuller Theory III.txt` lines 10324 and following;
`Inter-universal Teichmuller Theory IV.txt` lines 93-105 and 2330-2400.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe ua uv upi umon ui

namespace LeanFormal.IUT
namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

noncomputable section

/-! ## 1. The combined-def route is refuted at its dictionary pair -/

/-- **Alignment finding A1 (the N9 card, formalized).**  The two dictionary
hypotheses of `cor312CarrierSpec_epsilonComparison_of_dictionaries` -- and the
matching two fields of `Cor312CarrierRealizationSpec` -- are consumed at one and
the same point map `p` and one and the same scaling `D.scaling`, and that pair can
never both hold: at the triple `(1, 2, 3)` the chain would give
`log 6 <= logDegree (D.scaling * p 1 2 3) <= log 3`.  Hence the combined def has no
non-vacuous instantiation at any value-realized carrier datum, independently of
any concrete model; this is the precise N9 card at the def's own hypothesis
shapes.  The proof routes through the d5 model's single-map refutation
`iqCarrierModel_valueCarrier_no_jointDictionaries` (IQCarrierConcreteModel.lean);
the conclusion agrees with the e2 refutations
`cor312CarrierSpec_dictionaries_jointly_refutable` and
`cor312CarrierSpec_not_inhabited`. -/
theorem iqCarrierAlignment_jointDictionaries_refuted (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat -> Nat -> Nat -> I.ThetaPilotPoint v) :
    Not ((forall a b c : Nat, IsABCTriple a b c ->
        arithmeticWeight (abcRationalPoint a c) <=
          I.sourceLocalLogDegree v (D.scaling * p a b c)) ∧
      (forall a b c : Nat, IsABCTriple a b c ->
        I.sourceLocalLogDegree v (D.scaling * p a b c) <=
          Height.logHeight₁ (abcRationalPoint a c))) :=
  I.iqCarrierModel_valueCarrier_no_jointDictionaries v D.scaling p

/-- **Alignment finding A1b (cross-implementation agreement).**  The e2 package
refutation re-derived through the d5 model's refutation: any inhabitant of
`Cor312CarrierRealizationSpec` would exhibit a single point map satisfying both
dictionaries, which the model's refutation forbids.  This is a bridge between the
two independently written refutations, not a new mathematical fact (e2 already
proves the statement as `cor312CarrierSpec_not_inhabited`). -/
theorem iqCarrierAlignment_specPackage_refuted (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat -> Nat -> Nat -> I.ThetaPilotPoint v) (D0 : Real) :
    Not (Cor312CarrierRealizationSpec I v R n D p D0) :=
  fun S =>
    I.iqCarrierModel_valueCarrier_no_jointDictionaries v D.scaling p
      ⟨S.weightDictionary, S.pointHeightDictionary⟩

/-! ## 2. The reduced-form combination: weight dictionary plus a volume card -/

/-- **Alignment finding A2 (reduced form; labeled).**  The constructive sibling of
`cor312CarrierSpec_epsilonComparison_of_dictionaries` in which the refuted
point-height dictionary is replaced by the direct one-sided point-volume card
`(vol {D.scaling * p abc}).toReal <= (1 + eps) * weight + D1` (the replacement
shape recorded in the e2 judge table; the shape realized at the d5 calibration
model as `iqCarrierModel_hpoint` with `D1 = 0`).  Parameters, canonicalized hunit
constant, valuation bound, and conclusion type match the frozen def; the weight
dictionary keeps its frozen (c) shape; the supply-layer weight comparison,
the unconditional hsplit/hptfin, and the hunit normalization are discharged by
the same frozen reductions as in the frozen def.  This def does not modify,
replace, or re-interpret the frozen defs; it is the formal target for the pending
task-level decision on the repair shape. -/
def iqCarrierAlignment_epsilonComparison_of_weightDictionary_and_volumeCard (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat -> Nat -> Nat -> I.ThetaPilotPoint v)
    {D1 eps : Real} (heps : 0 <= eps)
    (hval : forall a b c : Nat, IsABCTriple a b c ->
      forall q, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) ->
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) <= 1 + eps)
    (weightDictionary : forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        I.sourceLocalLogDegree v (D.scaling * p a b c))
    (volumeCard : forall a b c : Nat, IsABCTriple a b c ->
      (I.sourceSetVolume v {D.scaling * p a b c}).toReal <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D1) :
    Cor312EpsilonArithmeticComparison
      (I.sourceUnitRegionHaarInterface v R n D) eps := by
  let hunitExists := cor312CarrierSpec_exists_hunitConstant I v R n D
  let D0 : Real := Classical.choose hunitExists
  have hD0 : 0 <= D0 := (Classical.choose_spec hunitExists).1
  have hB : ENNReal.ofReal D.degreeBound <=
      I.sourceHullVolume v R n + ENNReal.ofReal D0 :=
    (Classical.choose_spec hunitExists).2
  refine cor312GapAssembly_epsilonComparisonOfReducedInputs
    (D₁ := D1) (I.sourceUnitRegionHaarInterface v R n D) p heps hD0 hval ?_ ?_ ?_ ?_ ?_
  · exact I.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary v R n D p
      weightDictionary
  · exact I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume v R n D
      hD0 hB
  · exact I.cor312GapSupply_sourceInterface_hsplit v R n D p
  · exact fun a b c _ => I.cor312GapSupply_sourceInterface_hptfin v R n D p a b c
  · intro a b c habc
    change (I.sourceSetVolume v {D.scaling * p a b c}).toReal <=
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D1
    exact volumeCard a b c habc

/-- **Alignment finding A2a (additive reduced form; labeled).**  The additive
(version-2) sibling of
`iqCarrierAlignment_epsilonComparison_of_weightDictionary_and_volumeCard`: the
refuted uniform valuation bound is replaced by the approved additive input
`height ≤ (1 + ε) · weight + A` (contract `ABCHeightWeightAdditiveBoundV2`,
IUT IV Theorem A shape), the weight dictionary and the direct one-sided
point-volume card keep their shapes, and the conclusion is the additive
structure `Cor312EpsilonArithmeticComparisonAdditive` with the explicit
constant `A`.  The frozen defs and files are untouched. -/
def iqCarrierAlignment_epsilonComparisonAdditive_of_weightDictionary_and_volumeCard
    (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat -> Nat -> Nat -> I.ThetaPilotPoint v)
    {D1 eps A : Real} (heps : 0 <= eps)
    (hadd : forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c) <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (weightDictionary : forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        I.sourceLocalLogDegree v (D.scaling * p a b c))
    (volumeCard : forall a b c : Nat, IsABCTriple a b c ->
      (I.sourceSetVolume v {D.scaling * p a b c}).toReal <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D1) :
    Cor312EpsilonArithmeticComparisonAdditive
      (I.sourceUnitRegionHaarInterface v R n D) eps A := by
  let hunitExists := cor312CarrierSpec_exists_hunitConstant I v R n D
  let D0 : Real := Classical.choose hunitExists
  have hD0 : 0 <= D0 := (Classical.choose_spec hunitExists).1
  have hB : ENNReal.ofReal D.degreeBound <=
      I.sourceHullVolume v R n + ENNReal.ofReal D0 :=
    (Classical.choose_spec hunitExists).2
  refine cor312GapAssembly_epsilonComparisonOfAdditiveInput
    (D₁ := D1) (I.sourceUnitRegionHaarInterface v R n D) p heps hD0 hadd ?_ ?_ ?_ ?_ ?_
  · exact I.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary v R n D p
      weightDictionary
  · exact I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume v R n D
      hD0 hB
  · exact I.cor312GapSupply_sourceInterface_hsplit v R n D p
  · exact fun a b c _ => I.cor312GapSupply_sourceInterface_hptfin v R n D p a b c
  · intro a b c habc
    change (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D1
    exact volumeCard a b c habc

end

end OriginalInput
end Theorem311Source
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the N9 d5-e2 alignment: the proved refutation of the frozen
combined def's dictionary pair, the cross-implementation agreement, and the
labeled reduced-form combination with the direct volume card. -/
def iqCarrierRealizationAlignment : Obligation :=
  { id := "IUT-III.corollary-3.12-iq-carrier-realization-alignment"
    source :=
      "Corollary 3.12 carrier-layer task N9; companions: IQCarrierConcreteModel.lean " ++
        "(task d5), Cor312CarrierRealizationSpec.lean (task e2)"
    status := VerificationStatus.interface
    note :=
      "Alignment of the d5 concrete carrier model with the e2 frozen carrier spec. " ++
        "Proved: (A1) the dictionary pair of the frozen combined def " ++
        "cor312CarrierSpec_epsilonComparison_of_dictionaries is refuted at every " ++
        "value-realized carrier datum at one common point map and scaling (log 6 <= " ++
        "log 3 at the triple (1, 2, 3)), so the combined-def route has no " ++
        "non-vacuous instantiation; (A1b) the e2 package refutation re-derives " ++
        "through the d5 single-map refutation (cross-implementation agreement). " ++
        "Provided (reduced form, labeled): the constructive sibling " ++
        "iqCarrierAlignment_epsilonComparison_of_weightDictionary_and_volumeCard, " ++
        "replacing the refuted point-height dictionary by the direct one-sided " ++
        "point-volume card (the e2 judge-table replacement shape; the d5 " ++
        "calibration-model hpoint shape); the frozen defs and files are untouched " ++
        "and the replacement decision remains task-level. The model supplies " ++
        "neither the value-realized carrier data nor any paper carrier; the " ++
        "paper-level anchors are IUT III Corollary 3.12 (pp. 173-190) and IUT IV " ++
        "Theorem A (pp. 2-3)."
    dependsOn :=
      [ "IUT-III.corollary-3.12-iq-carrier-concrete-model-spike" ] }

end LeanFormal.IUT.Audit
