/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-! # A738 hull: audit of lana's Wall / EtaAlg (the last object of the chain)

Read-only audit of `tmp/online/lana-agents__iut/iut-main/Iut/Wall/*.lean` (12 files,
lana rev main).  The wall hypothesis (9-1) of the LANA report is the only unnamed
input left after the corrected Gap 1/2 chain:

* `EtaAlg D` is an interface for the eta-algorithm (IUT III, Theorem 3.11);
* `Wall D A` says: for every Theta-link, some choice `(iota, S)` has
  `etaAnab iota S = etaQ D` (i.e. `logVol (out iota S) = -|log q|`);
* lana proves `Wall A -> Corollary312Variant (concreteVariantData D)` and
  `Wall for all D -> ClassicalABC`; the wall itself is NOT proved and is the
  remaining mathematical input (LANA report calls it not reconstructible).

This file only records the requirements; it does not assume or axiomatize them.
Table rows are data (String triples/quadruples); no named structure is introduced.
No RETRACTED `hfull`/N-scaling file is referenced. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1WallRequirementAuditActual

/-- Fields of `Iut.Wall.EtaAlg D` (EtaAlg.lean:96-125). -/
def etaAlgFieldRows : List (String × String × String) :=
  [ ("model", "Pl D -> GMData", "opaque model etale-unit prime-strip {G_v acts on O_v^xmu}"),
    ("Side", "Type", "opaque Hodge theaters Theta^{+-ell}NF (IUT I)"),
    ("side_nonempty", "Nonempty Side", "there exists a Hodge theater (IUT I, Theorem A)"),
    ("etUnit", "Side -> EtUnitBPS model", "etale-unit BPS B(H) of a Hodge theater"),
    ("out", "(B : BPS) -> (h : Side) -> BPS.Iso B (thetaBPS h) -> Ind3 D -> Region D", "the eta-algorithm output M = 1.S = LGP.S in the container"),
    ("ind12_acts_on_S", "forall alpha iota, exists tau : Ind3 D ~= Ind3 D, forall S, out ((Iso.mk alpha refl).trans iota) S = out iota (tau S)", "(T1) Ind1/Ind2 act on the Ind3-choices (IUT III Thm 3.11(i))"),
    ("etUnitOnly", "exists f, forall iota S, out iota S = f iota.et S", "(T2) output depends only on the etale-unit portion"),
    ("realisation", "forall iota S, IsAdelic D (out iota S) and InHullOfImage D (out iota S)", "(T3) output is adelic and lies in the hull of a single (Ind1)-image of theta-pilot") ]

theorem etaAlgFieldRows_length : etaAlgFieldRows.length = 8 := rfl

/-- Expansion of the wall and its variants (EtaAlg.lean:173, Constraints.lean:222, MultiContainer.lean:88/295, MultiConstraints.lean:142). -/
def wallExpansionRows : List (String × String × String) :=
  [ ("Wall", "forall h1 h2, BPS.Iso (thetaBPS h1) (qBPS h2) -> exists iota S, etaAnab iota S = etaQ D", "the named input (9-1); never assumed"),
    ("wall_iff_forall", "Wall A <-> forall h1 h2, exists iota S, etaAnab iota S = etaQ D", "Theta-link data vacuous (BPS.connected, Remark 8.2.1)"),
    ("WallDistinct", "forall h1 h2, h1 != h2 -> forall gl, exists iota S, etaAnab iota S = etaQ D", "(C5) wall across distinct Hodge theaters; implies variant with DistinctSides"),
    ("WallOn L", "forall h1 h2, L h1 h2 -> forall gl, exists iota S, vol h2 (transport h1 h2 (out iota S)) = vol h2 (qRegionAt h2)", "multi-container wall along relation L"),
    ("Wall3", "WallOn (fun _ _ => True)", "multi-container wall for all pairs"),
    ("WallDistinct3", "WallOn (fun h1 h2 => h1 != h2)", "multi-container distinct wall"),
    ("SSIneq", "(sFactor (nC D) - 1) * |log q| <= logVol (hullOf (vcI D))", "Scholze-Stix inequality; wall is equivalent to it under LGPLaw/ThetaShift") ]

theorem wallExpansionRows_length : wallExpansionRows.length = 7 := rfl

/-- Module-by-module mathematical requirements and strength. -/
def wallModuleRows : List (String × String × String) :=
  [ ("EtaAlg.lean", "structure EtaAlg (8 fields), etaAnab, etaQ equivalence, Wall -> variant -> ClassicalABC", "interface + conditional chain; wall NOT proved"),
    ("BPS.lean", "GMData, GMIso, EtUnitBPS, EtUnitIso, ValBPS, ValBPS.Iso, PF, eta, BPS.connected", "abstract linear algebra; unconditional"),
    ("Pilots.lean", "sFactor, LocalDegrees, qVal, thetaVal (Finsupp/PF quotient), thetaLink, hexagon", "arithmetic/linear algebra; unconditional"),
    ("Rss.lean", "Region, IsAdelic, logVol, hullOf, thetaImage, InHullOfImage, InImage, Rss, rssEquiv, etaQ", "concrete local theory/measure; container and quotient"),
    ("QPilotRegion.lean", "labOne, powElt, pow, qRegion, logVol_qRegion, etaQReg", "scaling by powers of q; log-volume computed"),
    ("Scaling.lean", "Comp, Scaling (tensor units), act on regions, shift, qScale, negScale", "tensor-unit scaling; shift qScale = -|log q|"),
    ("Ind3.lean", "vcI, hullOf vcI, Ind3 choices (adelic S <= hull), Ind3.top/base, logVol bounds", "geometry/measure of log-shell container"),
    ("IdentifiedCopies.lean", "lgp, lgpRegion, lgpAt, IsAdelic phes, logVol_lgp, logVol_lgp_integral", "identified-copies log-volume law"),
    ("Constraints.lean", "C1 IPL, C2 SHESides, C3 SHEq (= Wall), C4 DistinctSides, C6 Multiradial, C7 SideDependent, C8 ValDependent, C9 APT, C10 HoloStructure, WallDistinct", "faithfulness constraints; C3 is the wall"),
    ("MultiContainer.lean", "MultiContainer, WallOn, Wall3, VolCompat, SSIneq, TransportRealisation", "multi-container model; Wall3 <-> Wall under VolCompat"),
    ("MultiConstraints.lean", "SHE3, Multiradial3, Alien3, DistinctKummer, WallDistinct3", "distortion models; wall3 <-> SSIneq"),
    ("Checks.lean", "NumericalWall, shadow lemma NumericalWall <-> Cor312, IsTrivial, LGPLaw, trivialAlg, exists_wall_iff", "faithfulness/trivial instance") ]

theorem wallModuleRows_length : wallModuleRows.length = 12 := rfl

/-- Concrete objects/inequalities needed to construct `EtaAlg D` and prove `Wall D A`. -/
def constructionStepRows : List (String × String × String) :=
  [ ("1. InitialThetaData D", "IUT I Def 3.1 (+Theta-link data)", "absent in our repo in lana form"),
    ("2. model : Pl D -> GMData and Hodge theaters Side", "etale-unit prime-strips + IUT I Theorem A", "absent; only our S1902 shell/log-volume machine"),
    ("3. etUnit/qBPS/thetaBPS", "LocalDegrees, qVal, thetaVal, PF = ker psi, thetaLink", "absent; needs value-group BPS formalization"),
    ("4. out : eta-algorithm", "for every BPS iso and Ind3-choice S, output LGP.S in container (IUT III Thm 3.11)", "biggest gap; no eta-algorithm in our repo"),
    ("5. Region/IsAdelic/logVol/hullOf", "LocalTheory.container placeSect nC, admissible regions, Haar log-volume", "partial: root-extension/product Haar, s1902 unit region, scaling laws"),
    ("6. Ind3 choices", "{S : Region D // IsAdelic S and S <= hullOf (vcI D)}", "partial: B1 gives point-null only; container hull absent"),
    ("7. Rss/etaQ/qRegion", "R_ss = adelic regions mod equal log-volume, etaQ : R_val -> R_ss", "absent; needs quotient by log-volume and qRegion"),
    ("8. T1/T2/T3", "ind12_acts_on_S, etUnitOnly, realisation (IsAdelic and InHullOfImage)", "absent (IUT III Thm 3.11 input)"),
    ("9. Wall proof", "forall h1 h2, exists iota S, etaAnab iota S = etaQ D (equiv. SSIneq)", "UNPROVED named input (9-1); LANA calls it not reconstructible"),
    ("10. wall -> variant", "lana variant_of_wall / literal_of_wall / classicalABC_of_wall", "conditional theorem already in lana") ]

theorem constructionStepRows_length : constructionStepRows.length = 10 := rfl

/-- Our repo correspondence / gaps. -/
def repoGapRows : List (String × String × String) :=
  [ ("Haar shell machine", "rootExtensionProductHaar, s1902 unit region/hull, rootHaarFactor", "partial for logVol/Region"),
    ("inverse scaling law", "Mzk1ScalingDirectionActual (badInvScale measure/log law)", "partial for Scaling.act/shift"),
    ("B1 point null", "Mzk1ProductHaarSingletonActual", "supports admissibility but not container hull"),
    ("bad-prime bookkeeping", "Mzk1BadPartActual (corrected N_bad)", "arithmetic support only"),
    ("theta-pilot log-volume", "S3137QThetaPilotLogVolumeReadingsActual (thetaPilotHullLogVolumeReal)", "partial analogue of RHSData.rhs/etaQ"),
    ("corrected Gap1/Gap2", "corrected-region chain + NatRadicalWeightBound", "does not construct EtaAlg or prove Wall"),
    ("missing core", "GMData/BPS, Hodge theaters, eta-algorithm out, Rss/etaQ, T1-T3, Wall", "the (9-1) gap; no repo object") ]

theorem repoGapRows_length : repoGapRows.length = 7 := rfl

/-- Audit summary: the last object of the chain is the wall (9-1); it is an
interface + an unproved Prop, not a theorem. -/
def wallAuditRows : List (String × String × String) :=
  [ ("last object", "Iut.Wall.Wall D A (9-1)", "NAMED input; not proved, not assumed"),
    ("interface", "Iut.Wall.EtaAlg D (8 fields: model/Side/side_nonempty/etUnit/out/ind12_acts_on_S/etUnitOnly/realisation)", "interface only"),
    ("conditional consequence", "Wall -> Corollary312Variant (concreteVariantData D) -> ClassicalABC", "lana EtaAlg.lean; conditional"),
    ("our status", "no EtaAlg constructed; no Wall proof; no assumption added", "INTEGRITY; ABC gate NOT passed") ]

theorem wallAuditRows_length : wallAuditRows.length = 4 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1WallRequirementAuditActual.etaAlgFieldRows_length
#print axioms LeanFormal.IUT.XiFPaper.Mzk1WallRequirementAuditActual.wallModuleRows_length
#print axioms LeanFormal.IUT.XiFPaper.Mzk1WallRequirementAuditActual.constructionStepRows_length

end LeanFormal.IUT.XiFPaper.Mzk1WallRequirementAuditActual