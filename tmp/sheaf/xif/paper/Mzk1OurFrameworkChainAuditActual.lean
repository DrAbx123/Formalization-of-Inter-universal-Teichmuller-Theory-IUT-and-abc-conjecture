/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FinalBoundarySzpiroActual
import tmp.sheaf.xif.paper.Mzk1ClassicalABCBridgeActual
import Mathlib.Tactic

/-! # A905: audit of OUR framework chain to ABCConjecture -/

/- AUTHORITY: our own objects/theorems; lana only for reference/cross-check.
No lana `SSIneq` dependency in this audit (its q-scaling issue is known).

GREEN RESULT INVENTORY (paper-normalized line; statuses from prior lane reports;
recompile status where marked):
- `Mzk1PaperNormMuActual`: logMuPaper = (1+[p=2]-1/e-r/n)log p; lower/upper bounds.
- `Mzk1PaperNormThetaActual`: thetaSumPaper = c_lana*A (proved identity).
- `Mzk1PaperNormDeficitActual`: paperDeficit def/expansion, deficit = ssCoeff*A - (sumMu+sumTheta),
  positive witness with e=1,r/n=1 (branch-B boundary).
- `Mzk1ThetaCancelActual` (stage4): sumTheta = ssCoeff*A => deficit = -sumLogMuPaper.
- `Mzk1SzpiroFromBoxActual`: c(l), 6c <= (l+5)/4, szpiro_from_box, eps(l) form.
- `Mzk1RDefinitionAuditActual`: r = p-power-unity-root EXPONENT; faithful coefficients
  p=2:0, p=5(zeta5):1/2, p=11:0; A-cancellation branch-A closure.
- `Mzk1ScaledThetaHull*`, `Mzk1ScaledPaper312Actual`, `Mzk1ScaledConsistencyCheckActual`,
  `Mzk1ScaledClosingShaActual`: scaled theta side and its consistency checks (prior green).
- `Mzk1Paper312*`: explicit 3.12 form (sF-1)A <= Lbar+Dbar; conditions; final bound.
- `Mzk1Cor312S3137AssemblyActual`: S3137 readings assembly (prior green).
- `Mzk1FinalBoundarySzpiroActual`: Szpiro6Shape def, ssIneqExplicit_to_szpiro6 etc.
- `Mzk1ClassicalABCBridgeActual`: ClassicalABCNatShape <-> ABCConjecture (PROVED, olean).

## Dependency graph (our framework)

1. faithful coefficients (r exponent)  -> deficit = -sumLogMuPaper <= 0  [green branch A]
2. deficit <= 0  -> paper-normalized SSIneq shape (sF-1)A <= V_norm  [green equivalence]
3. V_norm <= ((l+5)/4) logdf + C0  [MISSING: hull volume upper box]
4. volume upper + (sF-1)A <= V_norm -> Szpiro6 shape  [green arithmetic, T(l) chain]
5. Szpiro6 shape -> ABCConjecture  [MISSING: needs Cor312ToABCBridgeInterface /
   ABCFrontier construction; per A838 audit `Nonempty interface <-> ABCConjecture` and no
   construction exists in our repo OR in lana].
6. ClassicalABCNatShape <-> ABCConjecture  [PROVED, Mzk1ClassicalABCBridgeActual].

## Missing edges (precise)

(E1) dictionary: paper-normalized V_norm = our hull volume V (normalization bridge);
(E2) hull volume upper bound `V <= ((l+5)/4)*logdf + C0` (hull's open item);
(E3) `Nonempty Cor312ToABCBridgeInterface` or `ABCFrontier` (equivalent to ABC, no construction);
(E4) dictionary `qPilotRegion <= P -> (sF-1)A <= VolShell P` (A896).

STATUS: chain NOT closed.  No `ourFramework_ABCConjecture` theorem is produced: writing it
would require (E1)-(E3).  This audit is the honest dependency picture. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1OurFrameworkChainAuditActual

def chainEdges : List (String × String × String) :=
  [ ("faithful coeffs => deficit = -sumLogMuPaper <= 0", "green (branch A)", "GREEN") ,
    ("deficit <= 0 => (sF-1)A <= V_norm", "green equivalence", "GREEN") ,
    ("V_norm = hull volume V", "normalization dictionary", "MISSING (E1)") ,
    ("V <= ((l+5)/4)logdf + C0", "hull volume upper box", "MISSING (E2)") ,
    ("volume upper + SSIneq form => Szpiro6", "Mzk1SzpiroFromBoxActual + FinalBoundarySzpiro", "GREEN (arithmetic)") ,
    ("Szpiro6 => ABCConjecture", "interface/Frontier construction", "MISSING (E3) equivalent to ABC") ,
    ("ClassicalABCNatShape => ABCConjecture", "Mzk1ClassicalABCBridgeActual", "GREEN") ,
    ("qPilotRegion <= P => (sF-1)A <= VolShell P", "dictionary (A896)", "MISSING (E4)") ]

theorem chainEdges_length : chainEdges.length = 8 := rfl

/-- Final status predicate: the chain is closed iff all four missing edges are supplied. -/
def OurFrameworkChainClosed (E1 E2 E3 E4 : Prop) : Prop := E1 ∧ E2 ∧ E3 ∧ E4

theorem chain_closed_needs_edges (E1 E2 E3 E4 : Prop)
    (h : OurFrameworkChainClosed E1 E2 E3 E4) : E1 ∧ E2 ∧ E3 ∧ E4 := h

end LeanFormal.IUT.XiFPaper.Mzk1OurFrameworkChainAuditActual
