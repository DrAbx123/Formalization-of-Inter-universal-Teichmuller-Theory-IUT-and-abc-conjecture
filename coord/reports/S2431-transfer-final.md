# S2431 transfer final integration

Layer: O transfer chain.
Source objects: S2300VerlagerungNaturalRequired, S2179TransferCompatible, S2194/S2200.
Direction: PROVED S2179/S2194/S2200 from S2430 and S2371.

BUILT:
- S2431S2179TransferCompatible : S2179TransferCompatible.
- S2431S2194TransferCompatibilityRequired.
- S2431S2194TransferNaturalityRequired.
- S2431S2200TransferNaturalityRequired (pointwise from S2371).
- S2431S2200TransferCompatRequired.

EXIT=0; axioms propext, Classical.choice, Quot.sound; no sorryAx.
SHA256: 5AF800C36973F6D87CEDA37D2C51800244C859FB7E80E59C19B53B3B2F9F05CD
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2431TransferFinalActual.olean
olean SHA256: BF53CD101FA1DC639FC22F48922164A2F5FE0AC55C9273E671D87386EC21979F

Status: S2300 (S2371), S2179 (S2430), S2194, S2200 CLOSED. S2189 MuQZ MulAut data salvage subagent running.