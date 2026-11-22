/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-! # A745 hull: inventory of lana hull/log-volume lemmas usable for the lower bound

Read-only inventory of `Iut/Concrete/LocalConstruct/*` and
`Iut/Wall/{Scaling,QPilotRegion,Rss}.lean` (lana, rev main).  Goal: find proved
formulas for `logVol (hullOf D (vcI D))` that could yield the lower bound

  `(sFactor (nC D) - 1) * D.qPilot.absLogQ <= logVol D (hullOf D (vcI D))`  (SSIneq)

Table rows are data; no lana import is used here (lana oleans absent), so the
statements are recorded verbatim from the named source lemmas.  No claim of proof.
No RETRACTED file referenced. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullVolumeLemmaInventoryActual

/-- Definitions of the hull/log-volume layer (file:line in lana). -/
def definitionRows : List (String × String × String) :=
  [ ("Region", "Region D := forall i : Fin (VC D).proc.length, (VC D).AdmissibleRegion i", "Wall/Rss.lean:314"),
    ("IsAdelic", "IsAdelic D U := forall i, (hull D.placeSect (nC D)).IsAdmissible (U i)", "Wall/Rss.lean:319"),
    ("hullOf", "hullOf D U := (LocalTheory.hull D.placeSect (nC D)).hullFamily U", "Wall/Rss.lean:328"),
    ("logVol", "logVol D U := (LocalTheory.vol D.placeSect (nC D)).processionVol U", "Wall/Rss.lean:324"),
    ("packetVol", "packetVol i vQ U := sum over tuples c of tupleWeight vQ c * componentVol (tuple c) (proj c U)", "Concrete/LocalConstruct Packet.lean / Wall/Rss.lean:133"),
    ("globalVol", "globalVol U := finsum over RationalPlace of packetVol i vQ U", "Concrete/LocalConstruct Volume/Packet"),
    ("processionVol", "processionVol U := (sum_i globalVol (U i)) / proc.length", "Wall/Rss.lean / QPilotRegion"),
    ("archScale", "archScale t U: finite packets unchanged, infinite packet productRegion fun c => t • proj c (U i)", "Wall/Rss.lean:186-196"),
    ("vcIComp", "vcIComp i (.finite p) c = LocalTheory.shell K p (tuple c); vcIComp i .infinite c = LocalTheory.logShell K .infinite (tuple c)", "Wall/Ind3.lean:58-62"),
    ("vcI", "vcI := vcIAt: productRegion of vcIComp, integral off support (shell = integral at unramified good primes)", "Wall/Ind3.lean:80-123"),
    ("lgp", "lgp S := fun i => lgpAt i (S i); at finite p: image under x c => scaleElt i p c * x c; identity at infinity", "Wall/IdentifiedCopies.lean:145-169"),
    ("qRegion", "qRegion := pow (fun _ => 1) (labOne) integralRegion", "Wall/QPilotRegion.lean:314"),
    ("integralRegion", "integralRegion i := (VC D).integralAdmissible i (log-volume 0)", "Wall/Rss.lean:469") ]

theorem definitionRows_length : definitionRows.length = 13 := rfl

/-- Proved volume identities/inequalities relevant to the hull lower bound. -/
def formulaRows : List (String × String × String) :=
  [ ("componentVol_integral", "componentVol K vQ c (integral K vQ c) = 0", "LocalConstruct/Theory.lean:217"),
    ("componentVol_arch_scale", "componentVol K .infinite c (algebraMap t • integral) = Real.log t", "LocalConstruct/Theory.lean:229"),
    ("componentVol_prime_preimage", "componentVol ((p:Nat) * x)^-1 U = componentVol U + Real.log p", "LocalConstruct/Theory.lean:256"),
    ("componentVol_prod_incl_smul_integral", "componentVol ((prod incl(y)) • integral) = -(sum ordp y) * log p", "LocalConstruct/ScaleVolume.lean:118"),
    ("componentVol_hull_thetaShell_le", "archimedean hull of theta shell has componentVol <= card * log(sqrt 2 * pi) (UPPER)", "LocalConstruct/Theory.lean:380"),
    ("prop15", "indAut image of archimedean logShell subset (sqrt 2 * pi)^card * integral", "LocalConstruct/Theory.lean:371"),
    ("archLogShell_subset", "archLogShell subset (sqrt 2 * pi)^card * archIntegral", "LocalConstruct/ArchLogShell.lean:374"),
    ("haar_archLogShell_pos", "0 < haar .infinite c (archLogShell c)", "LocalConstruct/ArchLogShell.lean:401"),
    ("sum_tupleWeight", "sum over tuples of tupleWeight vQ c = 1", "Wall/Rss.lean:228"),
    ("packetVol_archScale_infinite", "packetVol i .infinite (archScale t U) = packetVol i .infinite U + log t", "Wall/Rss.lean:233"),
    ("globalVol_archScale", "globalVol (archScale t U) = globalVol U + log t", "Wall/Rss.lean:262"),
    ("processionVol_archScale", "processionVol (archScale t U) = processionVol U + log t", "Wall/Rss.lean:283"),
    ("logVol_archScale", "logVol (archScale t U) = logVol U + Real.log t", "Wall/Rss.lean:397"),
    ("logVol_pow_integral", "logVol (pow e lab integral) = -((sum_i e i)/nC) * |log q|", "Wall/QPilotRegion.lean:300"),
    ("logVol_qRegion", "logVol (qRegion D) = lhs = -|log q|", "Wall/QPilotRegion.lean:321"),
    ("logVol_integralRegion", "logVol (integralRegion D) = 0", "Wall/Rss.lean:474"),
    ("logVol_lgp", "IsAdelic S -> logVol (lgp S) = logVol (lgp integralRegion) + logVol S", "Wall/IdentifiedCopies.lean:281"),
    ("logVol_lgp_integral", "logVol (lgp integralRegion) = -(sFactor (nC D) * absLogQ)", "Wall/IdentifiedCopies.lean:444"),
    ("logVol_le_logVol_hullOf", "IsAdelic U -> IsAdelic S -> S <= hullOf U -> logVol S <= logVol (hullOf U) (UPPER)", "Wall/Ind3.lean:138"),
    ("logVol_le_rhs", "IsAdelic U -> InHullOfImage U -> logVol U <= rhs (UPPER)", "Wall/Rss.lean:374"),
    ("rhs_eq_logVol", "rhs = logVol (hullOf (thetaPilot)) (EQUALITY, theta side)", "Wall/Rss.lean:356"),
    ("logVol_surjective", "every real x is logVol of some adelic region", "Wall/Rss.lean:478") ]

theorem formulaRows_length : formulaRows.length = 22 := rfl

/-- Assessment: which lemmas can be used for a LOWER bound on logVol(hull(vcI))? -/
def lowerBoundApplicabilityRows : List (String × String × String) :=
  [ ("logVol_archScale", "only shifts by log t; for an Ind3-choice inside hull one needs 0 < t <= 1, so it can only DECREASE volume; cannot raise hull volume", "NOT usable as lower bound"),
    ("logVol_lgp / logVol_lgp_integral", "SSIneq becomes -|log q| <= logVol (lgp (hull(vcI))); LGP adds -s|log q|, still no lower bound on hull volume", "EQUIVALENT reformulation (used in A744)"),
    ("logVol_pow_integral / logVol_qRegion", "exact values only for pow/qRegion (q-side), not for hull(vcI)", "NOT about hull"),
    ("componentVol_prod_incl_smul_integral / componentVol_arch_scale", "exact volume for an explicit scaled integral a*O (elementary scalings); hull(vcI) is a hull region a*O with a given by least hull, but no formula/lower bound for a's unit modulus is provided", "PARTIAL: would need explicit least-hull scalar a and its unit modulus lower bound"),
    ("componentVol_integral = 0", "fixed finite point of reference; hull finite volume equals log(unitModulus of least-hull scalar) - 0, again needs the scalar", "PARTIAL"),
    ("packetVol_archScale_infinite / globalVol_archScale / processionVol_archScale", "exact archimedean shift (+log t); at infinity hull is (sqrt 2 pi)^card * B_I, giving card*log(sqrt 2 pi); this is only the archimedean UPPER hull in componentVol_hull_thetaShell_le", "UPPER bound only"),
    ("logVol_le_logVol_hullOf / logVol_le_rhs", "monotone UPPER bounds (subsets have smaller volume; InHullOfImage bounded by rhs)", "WRONG DIRECTION for SSIneq"),
    ("rhs_eq_logVol", "rhs is the volume of the hull of the theta-pilot image, NOT of hull(vcI); no comparison hull(vcI) vs theta image is proved", "NOT directly usable"),
    ("logVol_surjective / exists_ind3_logVol_iff", "existence of regions/Ind3 choices of any volume <= hull volume (via archScale down); existence of volume ABOVE hull volume is excluded; exact (s-1)|q| exists iff SSIneq", "CIRCULAR for SSIneq") ]

theorem lowerBoundApplicabilityRows_length : lowerBoundApplicabilityRows.length = 9 := rfl

/-- Precise remaining gaps and what would close them. -/
def gapRows : List (String × String × String) :=
  [ ("gap 1 (direct)", "explicit S : Ind3 D with logVol D S.1 = (sFactor (nC D) - 1) * absLogQ", "then ssiIneq_of_ind3_volume closes"),
    ("gap 2 (hull formula)", "identity or lower bound logVol (hullOf (vcI D)) >= (sFactor (nC D) - 1) * absLogQ", "then SSIneq directly"),
    ("gap 3 (theta comparison)", "prove hull(vcI) contains an (Ind1)-theta image and compare logVol, or rhs >= (s-1)|q|", "equivalent to variant; not in lana"),
    ("what lana supplies", "all definitions + exact volume of qRegion/lgp/integral + upper bounds for hull + existence of Ind3 volumes below hull + archimedean shift", "NO lower bound for hull(vcI)"),
    ("conclusion", "lana lemmas alone do not yield SSIneq; the lower bound / explicit S is the remaining input", "ABC gate NOT passed; no fake proof") ]

theorem gapRows_length : gapRows.length = 5 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullVolumeLemmaInventoryActual.definitionRows_length
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullVolumeLemmaInventoryActual.formulaRows_length
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullVolumeLemmaInventoryActual.gapRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HullVolumeLemmaInventoryActual