import LeanFormal.IUT.Audit.Status

/-! # IUTExternal12: existing-asset map for IUT external objects

Maps each external ref to existing assets (repo + external clones) and ownership.
STEP 0 verified: TauCeti local clone tmp/TauCeti (Apache-2.0; 20990 lean files) HAS
FieldTheory/FunctionField/** (including Belyi/{Basic,BranchPoints,Bundled,
Conjugation,GaloisAction,Polynomial,Radical}, Divisor/**, RiemannRoch/** including
Pencil.lean, Repartition/**, Place/**) and AlgebraicGeometry/WeilDivisor/** (Scheme/
LineBundle, Picard, RiemannRoch/{Basic,Finiteness,Space}, SerreDuality,
PrincipalParts/Cohomology, EulerCharacteristic, GlobalGeneration, ...), plus
AlgebraicGeometry/LineBundle/SerreDuality.lean.  FLT local clone
tmp/external/flt-lean + ported tmp/external/ported/flt{,2}/** (759 lean files;
source-only; oleans not built) and citable flat adapted copies AG_FLT_*.
TauCeti/FLT are separate lake projects: NOT importable directly -> adapt with
Apache-2.0 attribution (like AG_FLT_*), do not duplicate-port blindly.
No registry edits (frozen 14041).
-/

namespace LeanFormal.IUT.XiFPaper.IUTExternal12AssetsMapActual

/-- External ref -> existing asset bases + owner (data). -/
def IUTExternalAssetMap : List (String × String × String) :=
  [ ("[pGC]", "LeanFormal/IUT/IUTI,IUTII partial; pro-p groups (Mathlib post-port); no TauCeti/FLT equivalent", "stage4"),
    ("[GeoAn]", "LeanFormal/IUT/IUTI partial; IUTIII SourceCarrier abstractions; TauCeti category/sheaf infrastructure could adapt", "stage4"),
    ("[AbsAnb]", "ABCBridge/Geometry hyperbolic-curve place data; TauCeti FunctionField/Place/Extension/** (adapt, Apache-2.0)", "stage4"),
    ("[NCBel]", "stage4 Mzk1 statement; TauCeti FieldTheory/FunctionField/Belyi/** (Belyi Basic/BranchPoints/Bundled/Conjugation/GaloisAction/Polynomial/Radical) + Algebra/Polynomial/Belyi.lean + Analysis/Complex/RiemannSurface/BelyiPair.lean DIRECTLY relevant (adapt; Apache-2.0); GeometricCore remains D", "stage4 statement / mainline wiring"),
    ("[AbSc]", "LeanFormal/IUT/IUTII partial; TauCeti Galois/field infra adaptive", "stage4"),
    ("[SemiAn]", "IUTIII graphs/edge data; Mathlib combinatorial tools", "stage4"),
    ("[QuCnf]", "none dedicated; TauCeti AlgebraicGeometry/AdicSpace/** (adapt candidate)", "stage4"),
    ("[CbGC]", "IUTIII combinatorial pieces; TauCeti category/groupoid infra", "stage4"),
    ("[Config]", "none dedicated; TauCeti configuration-space-related infra (adapt candidate)", "stage4"),
    ("[FrdI-II]", "IUTIV ArithmeticDivisorDegree function layer only; no Frobenioid formalization (TauCeti no Frobenioid)", "stage4"),
    ("[EtTh]", "Theta-side SourceDefinition31Data/S3131/S3132; canonical rooted Q_C/H_C; no TauCeti/FLT equivalent", "stepxi"),
    ("[GenEll]", "GenEll00-13 P0 set; (i)=>(ii) proved; (ii)=>(i) paper-input; TauCeti Belyi + RR/Pencil assets supply geometric core (adapt); Mzk1 wiring pending", "mainline/abc/stage4"),
    ("[NodNon]", "none dedicated; TauCeti FunctionField/Place/Extension + CombinatorialAnabelian infra adaptive", "stage4"),
    ("[AbsTopI-III]", "AbsTopIII01-09 citable (07/08/09 integration; 05 DEEP named); tree S3137LogShellHaarLogVolumeScaling/S3137ThetaHullVolumeScaling", "hull/stage4"),
    ("[ExpEst]", "IUTIV Estimates/* (Section1/Section2/StepV*, ElementaryEstimates e1-e6); explicit-estimate corpus", "abc/stage4") ]

theorem IUTExternalAssetMap_length : IUTExternalAssetMap.length = 15 := rfl

/-- External clone asset rows (path, license, relevance, usability). -/
def IUTExternalCloneAssets : List (String × String × String × String) :=
  [ ("TauCeti", "tmp/TauCeti (local clone; Apache-2.0 LICENSE verified; 20990 lean files; separate lake project)", "AG03-AG08: WeilDivisor Scheme LineBundle/Picard/RiemannRoch/SerreDuality/PrincipalParts/EulerCharacteristic/GlobalGeneration + FieldTheory/FunctionField Divisor/RiemannRoch(inc Pencil)/Repartition/Place/Belyi", "ADAPT (Apache-2.0; not importable as-is; do not duplicate-port blindly)"),
    ("FLT local clone", "tmp/external/flt-lean (Apache-2.0; 1450 Definitions files)", "AG03/04/05/06/07: DivisorClassGroup/AdelicIndex/CechSectionsOfDivisor/SerrePairing/RiemannRochRows/curve base/finite map data", "ADAPT; flat citable copies AG_FLT_* exist for DivisorClassGroup/Repartitions/AdelicIndex/CoherentBaseChange/TwoChartCech/CechSectionsOfDivisor"),
    ("FLT ported tree", "tmp/external/ported/flt{,2}/** (759 lean files; source-only; oleans not built; duplicate-port risk)", "same as FLT", "SOURCE-ONLY: prefer flat AG_FLT_* citable set; coordinate before any further port"),
    ("Mathlib", "pinned Mathlib (Scheme/Over/Properties/Fiber/Limits/Normalization/ValuativeCriterion; FunctionField.lean:37/41/148; OrderOfVanishing.lean:35/52; RationalMap.lean; CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris})", "AG01/AG02/AG05 abstract cohomology", "REUSE"),
    ("PRs", "Mathlib PR #36218 merged (cohomology exact sequences); #43392 open (modules cohomology API); #41621 open draft (conditional RR)", "AG05/AG06", "TRACK") ]

theorem IUTExternalCloneAssets_length : IUTExternalCloneAssets.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.IUTExternal12AssetsMapActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: IUT external asset map. -/
def IUTExternalAssetMapRecord : Obligation :=
  { id := "INDEX.IUTEXTERNAL.asset-map"
    source := "coord/IUT-EXTERNAL-OBJECTS-INVENTORY.md; tauCeti tmp/TauCeti (Apache-2.0); FLT tmp/external/flt-lean + ported; pinned Mathlib; PRIOR-ART-INDEX G"
    status := VerificationStatus.interface
    note := "IUT EXTERNAL ASSET MAP (15 refs + 5 clone rows): STEP 0 verified TauCeti local clone (Apache-2.0; 20990 lean files) HAS FieldTheory/FunctionField Belyi/Divisor/RiemannRoch(inc Pencil)/Repartition/Place + AlgebraicGeometry/WeilDivisor Scheme LineBundle/Picard/RiemannRoch/SerreDuality/PrincipalParts/Cohomology/EulerCharacteristic/GlobalGeneration -> AG03-AG08 + NCBel geometric core ADAPT (separate lake, not directly importable; avoid blind duplicate port). FLT: local clone + ported tree source-only; flat AG_FLT_* citable copies preferred. Mathlib reuse + PRs tracked. Owners per inventory (stage4 most, stepxi EtTh, hull AbsTopIII, abc ExpEst/GenEll section1, mainline GenEll/NCBel wiring). No registry edits (frozen 14041)."
    dependsOn := ["IUTExternal12AssetsMapActual", "INDEX.IUTEXTERNAL.ids", "INDEX.AG.dependency-graph"] }

end LeanFormal.IUT.Audit
