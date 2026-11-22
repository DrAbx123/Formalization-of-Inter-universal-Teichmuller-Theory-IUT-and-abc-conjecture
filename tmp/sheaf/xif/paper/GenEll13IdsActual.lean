/-!
# GenEll13: GenEll P3 ids (data only; registry frozen 14041, no registry edits)

Ids for lattice (INDEX / statement ledger / citation lines) after the P3 batch.

* INDEX.GenEll.P3.IUTIVSection2-consumer -> GenEll09IUTIVSection2ConsumerActual:
  section2_card_id, theorem21_equiv_of_paperInput, iutIVSection2_cor23_bdClass,
  iutIVSection2_abcAll_of_genEllMainReduction, iutIVSection2RemainingPaperInputs.
  Replaces the Section2 [machine-gap] citation layer by an explicit conditional
  Cor 2.3 theorem (named paper-inputs; no assumed axiom).
* INDEX.GenEll.P3.H6-closure (interface level) -> GenEll10H6ClosureActual:
  h6_genEll_transfer, h6_genEll_BDClassOn, h6_genEll_caseII, h6ClosureRecord.
  Evidence: S3132IVGenEllShadowAdapterActual.genEll_transfer:43 (source-adapted
  vendor IUTStage1IUTIVAlgebra:9887-9928 shape).
* INDEX.GenEll.P3.route-interface -> GenEll11RouteInterfaceActual:
  GenEllRouteInterface, genEllRouteInterface, genEllRouteInterface_h6,
  genEllRouteInterface_p3, genEllRouteSlots.
* INDEX.GenEll.P3.step0 -> GenEll12Step0RecordActual.genEllP3Step0.
Reused (not re-proved; already CITABLE): GenEll01BasicActual, GenEll05Theorem21Actual,
GenEll08MainReductionActual, S3131BDClassCompositionActual, S3136BDClassChainToolActual,
S3131GenEllPaperInputActual, S3131GenEllInputDetailedActual, S3131GenEllEquivalenceShapeActual,
S3131GenEllShapeStatementsActual, S3131IUTIVTheoremAInputActual,
S3132IVGenEllShadowAdapterActual.
Class-B paper-inputs remaining: Thm 2.1 (ii)=>(i) + [Mzk1] + Thm 3.8 + Cor 4.3/4.4
(corpus lines: Thm 2.1 615-687; §3 738-1199; §4 1200-1425).
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.GenEll13IdsActual

/-- GenEll P3 ids: (index id, declarations, file). -/
def genEllP3Ids : List (String × String × String) :=
  [ ("INDEX.GenEll.P3.IUTIVSection2-consumer",
      "section2_card_id, theorem21_equiv_of_paperInput, iutIVSection2_cor23_bdClass, iutIVSection2_abcAll_of_genEllMainReduction, iutIVSection2RemainingPaperInputs",
      "GenEll09IUTIVSection2ConsumerActual.lean"),
    ("INDEX.GenEll.P3.H6-closure",
      "h6_genEll_transfer, h6_genEll_BDClassOn, h6_genEll_caseII, h6ClosureRecord",
      "GenEll10H6ClosureActual.lean"),
    ("INDEX.GenEll.P3.route-interface",
      "GenEllRouteInterface, genEllRouteInterface, genEllRouteInterface_h6, genEllRouteInterface_p3, genEllRouteSlots",
      "GenEll11RouteInterfaceActual.lean"),
    ("INDEX.GenEll.P3.step0", "genEllP3Step0", "GenEll12Step0RecordActual.lean") ]

end LeanFormal.IUT.XiFPaper.GenEll13IdsActual
