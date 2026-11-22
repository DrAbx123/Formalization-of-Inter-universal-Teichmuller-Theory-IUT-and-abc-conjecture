import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceContractedSupplyRealization
import LeanFormal.IUT.Audit.Status

/-!
  # The `O`-module layer and the compactness of `1,circ U` as named premises (Card-HULLREAL restart)

  Popper R4's wrap-up names the restart condition for the *positive* supply of the
  hull-bounding slot of the contracted route (`hScaling` of
  `SourceContractedSupplyRealization.lean`): the paper's mechanism is the
  [easily verified] compactness of the `1,circ U_{j,vQ}` together with the
  `O`-module (ring-of-integers) structure of `IQ(S±_{j+1}; n,circ D^vdash_{vQ})`.
  This module *names* the two premises as Lean data and closes everything that can
  be closed without the missing source geometry.

  ## Corpus anchors

  * IUT III, Corollary 3.12 proof, Step (xi) (corpus lines 10405-10411):
    "one concludes easily from the [easily verified] compactness of the
    `1,circ U_{j,vQ}` [where `j` in `|Fl|`, `vQ` in `VQ`], together with the
    definition of the log-volume, that the quantity `-|log(Theta)|` is finite".
    The tree-level counterpart of `-|log(Theta)|` is the hull log-volume
    (`sourceHullVolume`), whose finiteness is the output of the two premises.
  * IUT III, Remark 3.9.5, (i) (corpus lines 7658-7750): subsets containing a
    relatively compact subset of finite log-volume; the holomorphic hull as the
    smallest subset of the form `H`; the `lambda.O` scaling class with every
    component of `lambda` nonzero.
  * IUT III, Corollary 3.12 proof opening (corpus lines 10351-10358): the WLOG
    normalization `|log(q)| > 0`, `-|log(Theta)| < 0` -- the sign regime in which
    the degree-level contraction slot `hScaling` was refuted
    (`not_sourceScalingUnits_logDegree_nonpos_of_degreeFaithful`,
    `SourceContractionWlogReduction.lean:231-243`).
  * [AbsTopIII], Proposition 5.7, (i) (corpus lines 7915-7941): the normalized
    log-volume with the scaling law `mu^log(x.A) = mu^log(A) + x-dot-log` -- the
    normalization under which the `lambda.O` region plays the unit-region role.
  * In-tree: the audit note of `SourceImageHullVolume.lean` records that under
    `OriginalInput` alone the hull is unbounded
    (`sourceHolomorphicHull_logDegree_unbounded`); the ring-of-integers
    (`O`-module) structure is the missing ambient regularity.

  ## Route accounting (three routes, per the reduction pass)

  * R1 (selected; fully closed below): *absorb `lambda` into the region*.  The
    paper's input is `hull` inside `lambda.O` with `O` log-shell bounded --
    exactly the value-level shape of `ValueHullCompactnessInput`
    (`SourceHullInterfaceDischarge.lean:205-218`).  Taking the unit region of the
    Haar datum to be the scaled region `lambda.O` itself and the scaling to be
    `1` makes all six fields of `SourceUnitRegionHaarData` provable *without any
    nonpositivity constraint on `lambda`* (`sourceOModuleCompactness_haarData`:
    the region carries the scaling, and the Haar direction is discharged by the
    unit log-degree `0`).  This is the positive counterpart of the refuted
    `hScaling` slot: the sign constraint is irrelevant once the scaling is
    absorbed into the unit region -- the paper's own `lambda.O` normalization
    (Remark 3.9.5, (i)).  Consumer wiring mirrors the contracted route at both
    certificates.
  * R2 (resolved; conditional only): *direct contraction of the datum scaling*.
    `compactnessInput_to_sourceUnitRegionHaarData` (`IQCarrierHaarData.lean:237`)
    needs `degree lambda <= 0` on the datum's scaling; under pointwise degree
    faithfulness this is refutable for the constant scalings
    (`not_sourceScalingUnits_logDegree_nonpos_of_degreeFaithful`), so the
    constraint cannot be imposed on the general datum.  R1 removes the need for
    it; R2 remains recorded as the conditional form only.
  * R3 (infeasible; exact gap card below): *constructing* `SourceOModuleLayer`
    and `SourceOneCircUCompactness` for the realized carrier.

  ## Gap card (R3, exact)

  Missing items to construct the two premises from `OriginalInput`:
  (i) a topology (or normed `O`-module model) on `IQ(S±_{j+1}; n,circ
  D^vdash_{vQ})` on which "compactness of `1,circ U`" has content; (ii) the
  `O`-module (ring-of-integers) structure making `O` a compact open bounded
  region with a log-shell bound; (iii) the boundedness consequence "compact
  implies contained in some `lambda.O`" (needs the metric/topological model of
  (i)); (iv) the finite index family `|Fl| x VQ` realizing `1,circ U` as a finite
  union of compact images.  The tree has no topological structure on
  `I.ThetaPilotPoint v` and no module structure carrying `O`; the value
  realization collapses the index family to the single labelled image set
  (`possibleThetaPilotImageSet`), so the `VQ`-direction of the original index
  family is absorbed in the carrier `V` -- a value-level reduction that is
  recorded here rather than presented as the original object.  Under pointwise
  degree faithfulness the value-level datum is inconsistent
  (`not_nonempty_valueHullCompactnessInput_of_degreeFaithful`,
  `SourceHullInterfaceDischarge.lean:232-240`), so any such construction
  targets the actual (non-faithful) carrier only.  Nothing in this file claims
  the construction.

  ## `hweightvol` (scope statement)

  The positive supply of `hweightvol` does *not* route through this layer.  Its
  remaining premise is the point-level degree-weight dictionary
  (`cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary`,
  `Cor312ComparisonGapSupplyLayer.lean:174-186`), an arithmetic comparison on
  heights, with the unconditional form refuted by the negative calibration of
  `Cor312ComparisonGapReduction.lean:232` at the real-line carrier.  The restart
  condition named by Popper R4 concerns the `hScaling` side only; the
  `hweightvol` side is tracked separately and is not narrowed by this file.

  ## Verified claims of this file (nothing else)

  * The two named premises: `SourceOModuleLayer`, `SourceOneCircUCompactness`
    (no field is claimed to follow from `OriginalInput`; both are data).
  * The lambda-normalization bridge: from a datum of the compactness premise
    (whose `hull_subset_scaledRegionImage` field is the paper's boundedness
    consequence), the six fields of the Haar datum are filled with unit region
    `lambda.O` and scaling `1` (`sourceOModuleCompactness_haarData`), hence the
    hull log-volume is finite (`sourceOModuleCompactness_hullVolume_lt_top`).
  * Consumer wiring at both certificates of the bridge
    (`sourceOModuleCompactness_pointWiringCor312Conclusion`,
    `sourceOModuleCompactness_normalizedQ_cor312Conclusion`).

  ## Honesty notes

  * The bridge is a *conditional assembly*: its hypothesis is the named
    premise; no construction of the premise and no compactness argument are
    provided.
  * The scaling `1` of the produced Haar datum is the normalization convention
    (the paper's `lambda.O` class), not a claim about the sign of `degree
    lambda`; the sign requirement is confined to R2, which R1 bypasses.
  * Pointwise degree faithfulness makes the premise empty
    (`not_nonempty_valueHullCompactnessInput_of_degreeFaithful`); the bridge is
    therefore conditionally true but vacuous in that regime, as were the
    consumers it mirrors.  This file does not claim a nonempty datum.
  * The d5 model and the `Real`-line calibrations are consistency instances
    only; nothing here narrows the Card-HULLREAL distance.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The two named premises -/

/-- The `O`-module layer premise: a region (the role of the ring-of-integers
region `O` of the paper, on which the `O`-module structure makes the log-shell
bound meaningful) together with its log-degree bound.  A named datum, not a
construction: `SourceImageHullVolume.lean` records that no such bounded region
follows from `OriginalInput` alone. -/
structure SourceOModuleLayer (v : V) where
  /-- The ring-of-integers (`O`-module) region. -/
  unitRegion : Set (I.ThetaPilotPoint v)
  /-- The log-shell bound on the region. -/
  degreeBound : Real
  /-- Every point of the region has log-degree at most the bound. -/
  unitRegion_logDegree_le :
    forall y, y ∈ unitRegion -> I.sourceLocalLogDegree v y ≤ degreeBound

/-- The `1,circ U` compactness premise: the region `1,circ U` of the paper (the
union of the possible images over the finite label family), the containment of
the labelled theta-pilot images in it, the `O`-module layer, the scaling
`lambda` of the `lambda.O` class, and the boundedness consequence of the
[easily verified] compactness quoted in the proof of Corollary 3.12: the
holomorphic hull is contained in the scaled region `lambda.O`.  A named datum,
not a construction. -/
structure SourceOneCircUCompactness (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) where
  /-- The `1,circ U` region. -/
  oneCircU : Set (I.ThetaPilotPoint v)
  /-- The possible theta-pilot images lie in `1,circ U`. -/
  image_subset_oneCircU :
    I.possibleThetaPilotImageSet v R n ⊆ oneCircU
  /-- The `O`-module layer. -/
  layer : SourceOModuleLayer (I := I) v
  /-- The scaling `lambda` of the `lambda.O` scaling class. -/
  scaling : I.ThetaPilotPoint v
  /-- The boundedness consequence of the compactness of `1,circ U`: the
  holomorphic hull is contained in the scaled region `lambda.O`. -/
  hull_subset_scaledRegionImage :
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
      scaledRegionImage scaling layer.unitRegion

/-! ## 2. The lambda-normalization bridge -/

/-- R1: the lambda-normalization bridge.  From the compactness premise, the six
fields of the unit-region/Haar datum are filled by proofs: the unit region is
the scaled region `lambda.O` itself, the scaling is the unit `1`, the
log-degree bound is the sum of the scaling's log-degree and the layer bound,
the containment is the premise's boundedness consequence (reindexed by the unit
scaling), the region bound is additivity of the log-degree on `lambda.O`, and
the scaling direction is the unit log-degree `0`.  No nonpositivity constraint
on `lambda` is needed: the sign requirement of the direct route is absorbed
into the region. -/
def sourceOModuleCompactness_haarData (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (C : I.SourceOneCircUCompactness v R n) :
    I.SourceUnitRegionHaarData v R n :=
  I.compactnessInput_to_sourceUnitRegionHaarData v R n
    { scaling := 1
      unitRegion := scaledRegionImage C.scaling C.layer.unitRegion
      degreeBound := I.sourceLocalLogDegree v C.scaling + C.layer.degreeBound
      hull_subset_scaledRegionImage := by
        intro x hx
        exact ⟨x, C.hull_subset_scaledRegionImage hx, (one_mul x).symm⟩
      unitRegion_logDegree_le := by
        intro y hy
        obtain ⟨z, hz, rfl⟩ := (mem_scaledRegionImage_iff).mp hy
        rw [I.sourceLocalLogDegree_mul v C.scaling z]
        exact add_le_add le_rfl (C.layer.unitRegion_logDegree_le z hz) }
    (le_of_eq (I.sourceLocalLogDegree_one v))

/-- The bridge's unit region is the scaled region `lambda.O`. -/
theorem sourceOModuleCompactness_haarData_unitRegion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (C : I.SourceOneCircUCompactness v R n) :
    (I.sourceOModuleCompactness_haarData v R n C).unitRegion =
      scaledRegionImage C.scaling C.layer.unitRegion :=
  rfl

/-- The bridge's scaling is the unit `1` (the normalization convention). -/
theorem sourceOModuleCompactness_haarData_scaling (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (C : I.SourceOneCircUCompactness v R n) :
    (I.sourceOModuleCompactness_haarData v R n C).scaling = 1 :=
  rfl

/-- The hull log-volume is finite under the compactness premise (the tree-level
counterpart of the paper's `-|log(Theta)|` finiteness). -/
theorem sourceOModuleCompactness_hullVolume_lt_top (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (C : I.SourceOneCircUCompactness v R n) :
    I.sourceHullVolume v R n < ⊤ :=
  I.sourceUnitRegionHaarInterface_hull_logVolume_lt_top v R n
    (I.sourceOModuleCompactness_haarData v R n C)

/-! ## 3. Consumer wiring at the bridge certificates -/

/-- The canonical `q = -1` certificate route, closed from the compactness
premise through the lambda-normalization bridge. -/
theorem sourceOModuleCompactness_pointWiringCor312Conclusion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (C : I.SourceOneCircUCompactness v R n) (j : SignedLabel l.value)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((I.sourceUnitRegionHaarPointWiringCertificate v R n
          (I.sourceOModuleCompactness_haarData v R n C) j).toContract
        (I.sourceUnitRegionHaarPointWiringLinkEvidence v R n
          (I.sourceOModuleCompactness_haarData v R n C) j
          ipl she apt hipl hshe hapt)) :=
  I.sourceUnitRegionHaarPointWiringCor312Conclusion v R n
    (I.sourceOModuleCompactness_haarData v R n C) j ipl she apt hipl hshe hapt

/-- The paper-normalized-`q` certificate route, closed from the compactness
premise through the lambda-normalization bridge. -/
theorem sourceOModuleCompactness_normalizedQ_cor312Conclusion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (C : I.SourceOneCircUCompactness v R n) (j : SignedLabel l.value)
    (hθ1 : I.thetaValueAt (n.val : Int) 0 j < 1)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((I.sourceUnitRegionHaarNormalizedQ_certificate v R n
          (I.sourceOModuleCompactness_haarData v R n C) j hθ1).toContract
        (I.sourceUnitRegionHaarNormalizedQ_linkEvidence v R n
          (I.sourceOModuleCompactness_haarData v R n C) j hθ1
          ipl she apt hipl hshe hapt)) :=
  I.sourceUnitRegionHaarNormalizedQ_cor312Conclusion v R n
    (I.sourceOModuleCompactness_haarData v R n C) j hθ1 ipl she apt hipl hshe hapt

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the named `O`-module layer and `1,circ U` compactness
premises of the Card-HULLREAL positive supply restart: the two named data, the
lambda-normalization bridge to the unit-region/Haar datum, the hull-volume
finiteness corollary and the consumer wiring at both certificates. -/
def cardHullRealOModuleCompactness : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-omodule-compactness"
    source :=
      "IUT III, Corollary 3.12 proof, Step (xi) (corpus lines 10405-10411); " ++
        "Remark 3.9.5, (i) (corpus lines 7658-7750); Corollary 3.12 proof " ++
        "opening (corpus lines 10351-10358); [AbsTopIII], Proposition 5.7, (i) " ++
        "(corpus lines 7915-7941)"
    status := VerificationStatus.interface
    note :=
      "Named premises for the positive supply of the hull-bounding slot: " ++
        "SourceOModuleLayer (region with log-degree bound) and " ++
        "SourceOneCircUCompactness (the 1,circ U region, the image containment, " ++
        "the layer, the scaling lambda, and the containment of the holomorphic " ++
        "hull in lambda.O -- the boundedness consequence of the [easily " ++
        "verified] compactness quoted at corpus 10405-10411). The " ++
        "lambda-normalization bridge sourceOModuleCompactness_haarData assembles " ++
        "the six fields of SourceUnitRegionHaarData with unit region the scaled " ++
        "region lambda.O and scaling 1, so the hull log-volume is finite " ++
        "(sourceOModuleCompactness_hullVolume_lt_top) with no nonpositivity " ++
        "constraint on lambda -- the positive counterpart of the refuted " ++
        "hScaling slot. Consumer wiring mirrors the contracted route at the " ++
        "q = -1 and the paper normalized-q certificates. The premises are " ++
        "named, not constructed; the topological/ring-of-integers/finite-index " ++
        "items remain the exact gap card recorded in the module docstring. The " ++
        "hweightvol side does not route through this layer (arithmetic " ++
        "dictionary, refuted unconditional form, Cor312ComparisonGapReduction " ++
        "at the real-line carrier)."
    dependsOn :=
      [ "IUT-III.corollary-3.12-card-hullreal-contracted-source",
        "IUT-III.corollary-3.12-card-hullreal-contraction-wlog",
        "IUT-III.corollary-3.12-iq-carrier-haar-data",
        "IUT-III.corollary-3.12-iq-hull-interface-discharge" ] }

end LeanFormal.IUT.Audit