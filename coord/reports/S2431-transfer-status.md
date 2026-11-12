# transfer chain final status

## CLOSED (kernel clean, actual)
- S2300VerlagerungNaturalRequired: S2371HnatExplicitActual.S2371_verlagerung_natural.
- S2179TransferCompatible: S2430TorsionDescentSubagentActual.S2430_transferCompatible.
- S2422StageDescentRequired: S2430_stageDescentRequired.
- S2194TransferCompatibilityRequired: S2431TransferFinalActual.S2431S2194TransferCompatibilityRequired.
- S2194TransferNaturalityRequired: S2431TransferFinalActual.S2431S2194TransferNaturalityRequired.
- S2200TransferNaturalityRequired: S2431TransferFinalActual.S2431S2200TransferNaturalityRequired.
- S2200TransferCompatRequired: S2431TransferFinalActual.S2431S2200TransferCompatRequired.

Integration file: tmp/sheaf/xif/paper/S2431TransferFinalActual.lean
EXIT=0; SHA256 5AF800C36973F6D87CEDA37D2C51800244C859FB7E80E59C19B53B3B2F9F05CD
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2431TransferFinalActual.olean
olean SHA256: BF53CD101FA1DC639FC22F48922164A2F5FE0AC55C9273E671D87386EC21979F
axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## S2189MuQZMulAutData: NOT claimed / exact first missing
- B attempt tmp/sheaf/xif/paper/S2431MuQZMulAutSubagentActual.lean is INVALID (compile errors + sorryAx); not consumed.
- Salvage tmp/sheaf/xif/paper/S2432MuQZMulAutDoneActual.lean still does not compile; not kernel-clean.
- Mathematical obstruction: literal S2189MuQZMulAutData.action_compat is g-indexed using S2179StageConj p g H, but the actual stage conjugation composes anti-homically: (S2179StageConj g) o (S2179StageConj h) = S2179StageConj (h*g) (up to cast). Thus any literal g-indexed S2189MuQZMulAutData forces the commutativity input S2431EndComm (forall g h, A_(g*h)=A_(h*g)).
- Exact missing: prove S2431EndComm, or replace the literal structure by the honest g^{-1}-indexed action (corrected data). The corrected action's inverse/group-law/continuity/equivariance were attempted but not kernel-clean in the current B salvage.
- No unconditional S2189MuQZMulAutData is claimed.

## Other exact missing
- Joint continuity for a non-discrete topology on muQZ is not statable in the tree (no non-discrete topology declared).