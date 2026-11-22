import LeanFormal.IUT.Audit.Status

/-! # IUTExternal20: external-objects ledger with PROOF-STATUS dimension (Lead PRIORITY)

Bottom-up order: curves/function field -> divisors -> Cech H0/H1 -> RR -> Serde ->
Belyi/FiniteMapData -> GenEll -> AbsTopIII -> EtTh/Frd -> IUT IV section1.
Proof status: STATEMENT-ONLY = declarations assembled, no proof of the paper
statement; CLASS-A PROVED = elementary/unconditional theorem proved in tree;
COMPLETE-PROOF CITABLE = paper-level statement fully proved + checker CITABLE;
CLASS-B NAMED = paper-proved input registered, not proved in tree (DEEP = named
only).  Attached: ported FLT/TauCeti source paths, AG_* adaptation layer, checker
status.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.IUTExternal20ProofStatusActual

/-- Ordered external-object rows:
(layer, object, ref, proof-status, tree/adapted asset, checker status). -/
def IUTExternalProofStatus : List (String × String × String × String × String × String) :=
  [ ("1", "curves / function field / order of vanishing", "Mathlib AG01/AG02", "CLASS-A PROVED (Mathlib) + AG02FunctionField actual assembled", "Mathlib Scheme/Over/Properties/FunctionField:37/41/148 + OrderOfVanishing:35/52; AG02FunctionFieldActual, AG02bPrincipalDivisorActual", "checker CITABLE (AG02/AG02b)"),
    ("2", "divisors (Weil/Cartier/Pic)", "[AG03] (internal AG chain)", "ADAPTLAYER statement-only; FLT first layer complete-proof citable", "TauCeti AlgebraicGeometry/WeilDivisor/** + FieldTheory/FunctionField/Divisor/**; FLT tmp/external/flt-lean + AG_FLT_Def_AlgebraicCurve_DivisorClassGroup (CITABLE 72 decls)/Repartitions/AdelicIndex; ported tmp/external/ported/flt{,2}", "AG_FLT_* checker CITABLE; TauCeti source-only (separate lake)"),
    ("3", "Cech H0/H1 / principal parts cohomology", "[AG05]", "ADAPTLAYER partial; Mathlib abstract CLASS-A PROVED", "Mathlib CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris} (H/cohomologyPresheafFunctor/H.equiv0/Cech/MV); TauCeti WeilDivisor/Scheme/PrincipalParts/{Cohomology,FirstCohomology,RepartitionCohomology}/ResidueSequence; FLT AG_FLT_CechSectionsOfDivisor + CoherentBaseChange", "Mathlib reuse; AG_FLT CoherentBaseChange/CechSections checker-pending"),
    ("4", "Riemann-Roch", "[AG06]", "CLASS-B NAMED (TauCeti source PROVED upstream; not adapted yet) + PR #41621 draft", "TauCeti WeilDivisor/Scheme/RiemannRoch/{Basic,Finiteness,Space,GeometricallyIntegral} + FieldTheory/FunctionField/RiemannRoch/** (Basic/Genus/ClassNumber/Pencil/SectionRing); FLT RiemannRochRows", "TauCeti source-only; no adaptation file yet"),
    ("5", "Serre duality", "[AG07]", "CLASS-B NAMED (TauCeti source PROVED upstream; not adapted yet)", "TauCeti AlgebraicGeometry/LineBundle/SerreDuality + WeilDivisor/Scheme/SerdeDuality; FLT SerrePairing", "source-only; adaptation pending"),
    ("6", "Belyi / FiniteMapData / GeometricCore", "[NCBel]", "STATEMENT-ONLY (Mzk1 statements) + Belyi infra CLASS-B NAMED (TauCeti) + GeometricCore D", "TauCeti FieldTheory/FunctionField/Belyi/** + Algebra/Polynomial/Belyi + RiemannSurface/BelyiPair; FLT SmoothProperCurveBase/FiniteMapData; GenEll05 Theorem21ReductionInputs (noncriticalBelyiExists named); stage4 Mzk1 statement", "Mzk1 statement file in progress; TauCeti source-only"),
    ("7", "GenEll Theorem 2.1 / P0-P3", "[GenEll]", "CLASS-A PROVED for (i)=>(ii); CLASS-B NAMED for (ii)=>(i); P3 interface assembled", "GenEll00-13 P0 set; GenEll05 theorem21_i_implies_ii PROVED; Theorem21_ii_implies_i_required named; GenEll09-13 P3 interfaces; GenEll10StatementLedger/11Ids/12Citations/13DepMap (lattice)", "GenEll10-13 checker CITABLE; P0 files mostly CITABLE"),
    ("8", "AbsTopIII (log-shell/Prop5.7/Cor5.10/Prop5.8)", "[AbsTopIII]", "CLASS-A PROVED concrete side (01/03/04/07/08/09) + DEEP NAMED (05 Prop5.8)", "AbsTopIII01LogShell/03Cor510/04LogFrobenius/07VolumeLogShellBridge/08PvAdicScaling/09ThetaHullScaling citable; AbsTopIII05ReconstructionInputs named; AbsTopIII10/11 ledger (lattice); tree S3137LogShellHaarLogVolumeScaling/S3137ThetaHullVolumeScaling", "hull assets checker CITABLE; 05 deep named only"),
    ("9", "EtTh / Frobenioid I-II", "[EtTh]/[FrdI-II]", "STATEMENT-ONLY (statement layers in progress); deep Frobenioid theory CLASS-B NAMED", "stepxi EtFrd05IdsActual.etFrdIds (INDEX.ETTH.statement/.deep-inputs/.tree-reuse/.route-wiring; INDEX.FRD.statement/.reuse; INDEX.ETTH.FRD.step0); tree Theta-side SourceDefinition31Data/S3131/S3132; IUTIV ArithmeticDivisorDegree function layer", "stepxi batch EXIT0 + checker CITABLE (probe _EtThFrdProbe 165942)"),
    ("10", "IUT IV section1 / Thm 1.10 layer", "[IUTchIV]", "STATEMENT-ONLY + machine-gap named", "stepxi S3171IdsActual.s3171Ids (INDEX.IUTIV.Thm110.display/.inputs/.uniform-height/.FLT-support/.skeleton-align/.step0; SHA 6A53C7E6); IUTIV/Estimates/Section1.lean; FLT support assets", "stepxi batch EXIT0 + checker CITABLE (probe _S3171BatchProbe 164512)"),
    ("11", "ExpEst (Stage 5 explicit estimates)", "[ExpEst]", "CLASS-A PROVED partial (elementary estimates e1-e6) + CLASS-B NAMED (PNT inputs)", "IUTIV/Estimates/ElementaryEstimates e1-e6; Section1/Section2/StepV*; ExpEst02 (abc) 7 decls honest PNT paper-inputs", "ExpEst02 checker CITABLE 3BB83606"),
    ("12", "AG adaptation layer statuses", "AG_FLT_*/TauCeti/FLT ported", "MIXED: AG_FLT_DivisorClassGroup/Repartitions/AdelicIndex/CoherentBaseChange COMPLETE-PROOF CITABLE; TwoChartCech/CechSections pending; RR/Serde/Belyi source-only", "flat AG_FLT_* (tmp/sheaf/xif/paper); source tmp/external/flt-lean + tmp/external/ported/flt{,2}; source tmp/TauCeti (Apache-2.0)", "AG_FLT_* checker CITABLE (qpilot); ported oleans not built"),
    ("13", "layer-2 new stepxi assets", "AG04/GenEll14/Indet05", "CLASS-A PROVED on current declarations + checker CITABLE", "AG04FiniteDivisorActual (AG04 finite divisors+degree), AG04bResidueFieldActual, GenEll14P3WiringActual (consumes GenEll05bWiringMap), Indet05RouteMultiradialClassActual (route Ind1/2/3)", "stepxi reports EXIT0 + checker CITABLE; layer-2 integration") ]

theorem IUTExternalProofStatus_length : IUTExternalProofStatus.length = 13 := rfl

end LeanFormal.IUT.XiFPaper.IUTExternal20ProofStatusActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: external-objects proof-status ledger. -/
def IUTExternalProofStatusRecord : Obligation :=
  { id := "INDEX.IUTEXTERNAL.proof-status"
    source := "Lead PRIORITY; coord/IUT-EXTERNAL-OBJECTS-INVENTORY.md; TauCeti tmp/TauCeti; FLT tmp/external/flt-lean+ported; AG_* files; stepxi S3171/EtFrd/GenEll14/AG04/Indet05"
    status := VerificationStatus.interface
    note := "EXTERNAL OBJECTS LEDGER WITH PROOF STATUS (13 ordered rows, bottom-up: curves/function field -> divisors -> Cech H0/H1 -> RR -> Serde -> Belyi/FiniteMapData -> GenEll -> AbsTopIII -> EtTh/Frd -> IUT IV section1; plus AG adaptation statuses and layer-2 assets): statuses STATEMENT-ONLY / CLASS-A PROVED / COMPLETE-PROOF CITABLE / CLASS-B NAMED (+DEEP named). Attached ported FLT/TauCeti source paths, AG_FLT_* adaptation layer, checker statuses. Deep inputs (GeometricCore, Prop5.8, Frobenioid deep theory) named only. No registry edits (frozen 14041)."
    dependsOn := ["IUTExternal20ProofStatusActual", "IUTExternal10IndexIdsActual", "IUTExternal12AssetsMapActual"] }

end LeanFormal.IUT.Audit
