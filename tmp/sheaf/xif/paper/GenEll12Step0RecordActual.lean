/-!
# GenEll12: STEP 0 deep-search record for the P3 batch (policy §7.10; data only)

Queries (tools/xif_deep_search.ps1 -Query):
  Section2|machine-gap|genEll_transfer|GenEllTheorem21|CompactlyBounded|BDClassInequality|MainReduction|Theorem21|IUTIVTheoremA
  weight_le_theta|hull_le_theta|CardAMPLThetaBoundSupply|hpoint|hpoint|dictionary|heightVolume|GenEll|LGPModelSourceClauseMissing|H4|H5|H6|R2|comparisonRegion|measure-invariance
Hits: LeanFormal 8 + 220; tmp/sheaf/xif/paper 85 + 1055; vendor 18 + 104; corpus 83; gap-exploration 3.
Sections read in coord/PRIOR-ART-INDEX.md: A (model), B (R1/M1/M2b/F4), C (Theta side),
D ((b)/(c)), E (paper citations), F (traps), G (paper-level additions).
Reuse decisions for the P3 integration (no re-proof):
* IUT IV §2 card -> LeanFormal/IUT/IUTIV/Estimates/Section2.lean:100 iutIVSection2 Obligation
  + :111/124/190/225/252/325/353/386/393 theta bounds (reuse; consumed by GenEll09).
* GenEll Thm 2.1 statement + (i)=>(ii) proved -> GenEll05Theorem21Actual (reuse).
* GenEll main reduction consumer interface -> GenEll08MainReductionActual (reuse).
* BD-class/GenEll basic defs -> GenEll01BasicActual (BDClassOn, PaperHeight/LogDiff/LogCond,
  CompactlyBoundedSubset) (reuse).
* GenEll shadow transfer (H6) -> S3132IVGenEllShadowAdapterActual.genEll_transfer:43 +
  exists_lowerBound:57 + discrepancy_bounded_below:67 (reuse).
* BD-class algebra -> S3131BDClassCompositionActual (IsBDLe refl/add_right/trans) and
  S3136BDClassChainToolActual (IsBDLe/IsBDEq) (reuse; not re-proved).
* Existing GenEll statement assets listed in the plan (S3131GenEllPaperInputActual,
  S3131GenEllInputDetailedActual, S3131GenEllEquivalenceShapeActual,
  S3131GenEllShapeStatementsActual, S3131IUTIVTheoremAInputActual) (reuse).
* vendor IUTStage1IUTIVAlgebra.lean:8056/:9900 = source-only (separate lake; cannot import);
  the shape is already re-declared in S3132IVGenEllShadowAdapterActual, so no vendor import needed.
New precedents appended to coord/PRIOR-ART-INDEX.md (section G, 2026-11-10 stepxi GenEll P3).
Pins: registry frozen 14041; no intermediate reopen (user: only paper-level theorem once).
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.GenEll12Step0RecordActual

/-- STEP 0 record for the GenEll P3 batch: (query, hits summary, reuse decision). -/
def genEllP3Step0 : List (String × String × String) :=
  [ ("Section2|machine-gap|genEll_transfer|GenEllTheorem21|CompactlyBounded|BDClassInequality|MainReduction|Theorem21|IUTIVTheoremA",
      "LeanFormal 8 / paper 85 / vendor 18",
      "reuse: Section2:100 card + GenEll05/08 + S3132 shadow"),
    ("weight_le_theta|hull_le_theta|CardAMPL|hpoint|dictionary|heightVolume|GenEll|LGPModelSourceClauseMissing|H4|H5|H6|R2|comparisonRegion|measure-invariance",
      "LeanFormal 220 / Iut 14 / paper 1055 / vendor 104 / corpus 83 / gap 3",
      "reuse: CardAMPLThetaBoundSupply:78/94/193; IQCarrierConcreteModel:346/386; GapReduction:306"),
    ("BDClassOn|IsBDLe|IsBDEq", "S3131BDClassCompositionActual + S3136BDClassChainToolActual",
      "reuse (no re-proof of BD algebra)"),
    ("GenEll shadow/genEll_transfer", "S3132IVGenEllShadowAdapterActual:43/57/67",
      "reuse for H6 interface closure") ]

end LeanFormal.IUT.XiFPaper.GenEll12Step0RecordActual
