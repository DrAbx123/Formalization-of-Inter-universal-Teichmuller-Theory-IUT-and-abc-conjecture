import LeanFormal.IUT.Audit.Status

/-! # AG90: Mathlib capability matrix for the AG infrastructure (lattice ledger)

STEP 0 prior-art: deep search AG00MathlibAudit|AG01CurveFoundations|AG02FunctionField|
AG03DivisorsSections|OrderOfVanishing|FunctionField|basepoint-free|pencil|Serre|
RiemannRoch|GeometricCore -> 42 LeanFormal + 17 local-cft + 467 paper + 22 vendor +
152 corpus hits; no AG00-AG03 files exist yet (to be written by AG stream); Mathlib
paths audited below.  No re-proof; no axioms; registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.AG90MathlibAuditActual

/-- Mathlib capability matrix rows: (capability, Mathlib asset/decl, availability, gap/consumer). -/
def AGMathlibCapabilityMatrix : List (String × String × String × String) :=
  [ ("curve foundations (schemes/proper/smooth/integral)", "Mathlib/AlgebraicGeometry/Scheme.lean; Over.lean; Properties.lean; Fiber.lean; Limits.lean; Normalization.lean; ValuativeCriterion.lean", "AVAILABLE", "AG01CurveFoundations: build curve/geometric-curve layer on these"),
    ("function field", "Mathlib/AlgebraicGeometry/FunctionField.lean:37 Scheme.functionField; :41 Scheme.germToFunctionField; :55 germ_injective_of_isIntegral; :65 scheme.germToFunctionField_injective; :148 functionField_isFractionRing_of_isAffineOpen", "AVAILABLE", "AG02FunctionField: re-export/refine, no rebuild"),
    ("order of vanishing", "Mathlib/AlgebraicGeometry/OrderOfVanishing.lean:35 ordHom; :52 ord (coheight-1 points)", "AVAILABLE (coheight-1)", "AG02OrderOfVanishing: re-export; divisor valuations"),
    ("rational maps", "Mathlib/AlgebraicGeometry/RationalMap.lean", "AVAILABLE", "AG03: maps/dominant rational maps for divisors"),
    ("divisors (Weil/Cartier)", "TAUCETI tmp/TauCeti (Apache-2.0; local clone; 20990 lean files): AlgebraicGeometry/WeilDivisor/{Basic,Order,Principal/**,FractionalIdealDivisor,LinearSystem,FiniteSum}, WeilDivisor/Scheme/{Basic,Degree,Order,Place,Principal,Invertible,LocallyPrincipal,Picard}; FieldTheory/FunctionField/Divisor/** + Place/** (ADAPT); FLT adapted AG_FLT_Def_AlgebraicCurve_DivisorClassGroup (CITABLE 72 decls: Divisor/degree/Pic/Pic0) + Repartitions + AdelicIndex (CITABLE 68 decls)", "REUSE/ADAPT (TauCeti + FLT adapted)", "AG03DivisorsSections: TauCeti Weil divisor/line bundle theory directly adaptable; FLT first layer citable; separate lake -> adapt with Apache-2.0 attribution"),
    ("line bundles / invertible sheaves", "TAUCETI AlgebraicGeometry/WeilDivisor/Scheme/{LineBundle,Picard,PicZero,TensorProduct,Invertible,LocalTriviality}; AG_FLT_DivisorClassGroup (Pic/Pic0 adapted CITABLE) + AdelicIndex; Mathlib Modules/Sheaf/Tilde; PR #43392", "REUSE/ADAPT (TauCeti + FLT)", "AG04LineBundles: TauCeti line-bundle/Picard theory adaptable; FLT Pic/Pic0 citable; sections via Cech pending"),
    ("sheaf sections / global sections", "Mathlib Modules/Sheaf.lean; Modules/Tilde.lean (tilde sheaf sections); Mathlib/CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}.lean: H/cohomologyPresheafFunctor/H.equiv0/cech; FLT Def_AlgebraicCurve_CechSectionsOfDivisor", "PARTIAL-REUSE", "AG03/AG04: sections H^0 via Mathlib abelian-sheaf cohomology + FLT Cech sections (adapt)"),
    ("sheaf cohomology (abstract/cech/MV)", "TAUCETI AlgebraicGeometry/WeilDivisor/Scheme/{PrincipalParts/Cohomology,FirstCohomology,RepartitionCohomology,ResidueSequence/**,SerreDuality,Sheaf,EulerCharacteristic}; Mathlib SheafCohomology Basic/Cech/MV; AG_FLT CoherentBaseChange (EXIT0) + CechSectionsOfDivisor (adapted); PR #36218 merged, #43392 open", "REUSE/ADAPT (TauCeti + FLT + Mathlib)", "AG05Cohomology: TauCeti principal-parts/cohomology + FLT Cech give coherent H0/H1; adapt"),
    ("Riemann-Roch", "TAUCETI AlgebraicGeometry/WeilDivisor/Scheme/RiemannRoch/{Basic,Finiteness,Space,GeometricallyIntegral} + FieldTheory/FunctionField/RiemannRoch/** (Basic/Genus/ClassNumber/Pencil/SectionRing); FLT Def_AlgebraicCurve_RiemannRochRows; PR #41621 open draft; chip-firing RR graphs arXiv 2606.16679", "REUSE/ADAPT (TauCeti primary)", "AG06RiemannRoch: TauCeti RR (scheme + function-field, incl Pencil) directly adaptable; FLT RR rows secondary; PR tracked"),
    ("Serre duality", "TAUCETI AlgebraicGeometry/LineBundle/SerreDuality.lean + AlgebraicGeometry/WeilDivisor/Scheme/SerreDuality.lean; FLT Def_AlgebraicCurve_SerrePairing", "REUSE/ADAPT (TauCeti primary)", "AG07SerreDuality: TauCeti SerreDuality adaptable; FLT pairing secondary"),
    ("basepoint-free pencil", "TAUCETI FieldTheory/FunctionField/RiemannRoch/Pencil.lean + AlgebraicGeometry/WeilDivisor/LinearSystem/** + GlobalGeneration + FLT SmoothProperCurveBase/FiniteMapData", "REUSE/ADAPT (TauCeti primary)", "AG08BasepointFreePencil: TauCeti pencil/linear-system theory directly adaptable; FLT finite-map data secondary; no general Belyi formalization"),
    ("Mzk1 GeometricCore (noncritical Belyi/curves)", "paper papers/motizuki_corpus/text/Noncritical Belyi Maps.txt; TAUCETI FieldTheory/FunctionField/Belyi/** (Basic/BranchPoints/Bundled/Conjugation/GaloisAction/Polynomial/Radical) + Algebra/Polynomial/Belyi.lean + AlgebraicTopology/ThricePuncturedSphere FilledCover/AnalyticBelyiPair + Analysis/Complex/RiemannSurface/BelyiPair.lean (ADAPT)", "REUSE/ADAPT for Belyi infra; D residual for GeometricCore", "AG09Mzk1GeometricCore: TauCeti Belyi infra adaptable; noncritical GeometricCore itself remains D paper-input"),
    ("FLT adaptation audit", "AG00bFLTAssetAuditActual.lean (EXIT0; module->AG layer mapping data + rfl facts; probe no-axiom); flat naming AG_FLT_<FLT module>; import rewrite only Definitions.* -> tmp.sheaf.xif.paper.AG_FLT_*; namespaces preserved", "REALIZED audit", "tracks adapted FLT set: DivisorClassGroup/Repartitions/AdelicIndex/CoherentBaseChange green; TwoChartCech/CechSectionsOfDivisor pending; SerrePairing/RiemannRochRows/SmoothProperCurveBase/FiniteMapData next"),
    ("TauCeti asset base", "tmp/TauCeti (local clone; Apache-2.0 LICENSE verified; 20990 lean files; separate lake project, not directly importable): AlgebraicGeometry/WeilDivisor/** (LineBundle/Picard/RiemannRoch/SerreDuality/PrincipalParts/Cohomology/EulerCharacteristic/GlobalGeneration/LinearSystem), FieldTheory/FunctionField/** (Divisor/Place/RiemannRoch/Pencil/Belyi/Repartition)", "REUSE/ADAPT (Apache-2.0; adapt with attribution; do not blind duplicate-port)", "AG03-AG08 + NCBel Belyi infra: primary source (TauCeti) over FLT for scheme-level divisor/cohomology/RR/pencil/Belyi"),
    ("IUT formalization roadmap / context", "Mochizuki-Hoshi-Yamashita-Yang, Formalization of IUT (2026-04) papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt + kurims URL; LANA report (papers/LANA_report_202607.pdf; text tmp/external/lana_report_202607.txt; github.com/katobungen/LANA_report_202607); Stoll, Formalizing Heights in Arithmetic Geometry (talk); Cambridge Brauer group/group cohomology in Lean4 seminar", "CONTEXT/planning", "AG00/roadmap alignment: four-triangle decomposition (BPS/etHT/dsc/HDD/SHE/IPL/APT/Ind1,2,3, Thm 3.11/3.11.5/Cor 3.12); height layer reference; Brauer/group cohomology reference") ]

theorem AGMathlibCapabilityMatrix_length : AGMathlibCapabilityMatrix.length = 15 := rfl

end LeanFormal.IUT.XiFPaper.AG90MathlibAuditActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: AG Mathlib capability matrix. -/
def AGMathlibCapabilityMatrixRecord : Obligation :=
  { id := "INDEX.AG.mathlib-capability-matrix"
    source := "Mathlib/AlgebraicGeometry/{Scheme,Over,Properties,Fiber,Limits,Normalization,ValuativeCriterion,FunctionField,OrderOfVanishing,RationalMap,Modules/*,Sites/ElladicCohomology}.lean; corpus Noncritical Belyi Maps"
    status := VerificationStatus.interface
    note := "AG CAPABILITY MATRIX (15 rows, incl. TauCeti + FLT adaptation): AVAILABLE from Mathlib = curve foundations (Scheme/Over/Properties/Fiber/Limits/Normalization/ValuativeCriterion), function field (FunctionField.lean:37 Scheme.functionField, :41 germ, :55/:65 injectivity, :148 fraction ring), order of vanishing (OrderOfVanishing.lean:35 ordHom, :52 ord, coheight-1), rational maps (RationalMap.lean). PARTIAL-REUSE = abstract sheaf cohomology Mathlib/CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}.lean (H/cech/MV; not only ell-adic) + module sheaves, and external FLT anthropics/fermats-last-theorem assets (Apache-2.0; divisor class group/adelic index/Cech sections/Serre pairing/RR rows/curve base/finite map data) for AG03-AG07; upstream PRs #36218 merged (sheaf cohomology exact sequences), #43392 open (modules cohomology API), #41621 open draft (conditional RR). TO BUILD = basepoint-free pencil construction + Mzk1 GeometricCore (paper-input; no Belyi formalization). No re-proof; no axioms; registry frozen 14041."
    dependsOn := ["AG90MathlibAuditActual"] }

end LeanFormal.IUT.Audit
