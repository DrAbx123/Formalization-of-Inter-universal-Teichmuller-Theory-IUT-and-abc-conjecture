# S2194: transfer compatibility proof surface

Layer: O (muQZ conjugation / transfer).
Source object: Stage p H, toStage/Verlagerung, S2179StageConj.
Domain: transfer compatibility.
Direction: exact missing surface; no proof of naturality.

BUILT:
- S2194TransferCompatibilityRequired = S2179TransferCompatible.
- S2194TransferNaturalityRequired: exact naturality statement with actual S2179StageConj.
- S2194MuQZMulAutRequired = S2189MuQZMulAutRequired.
- S2194TransferToMulAutRequired: exact reduction type transfer compatibility -> MulAut data.

MISSING exact: naturality of transfer under conjugation (S2194TransferNaturalityRequired / S2179TransferCompatible). Verlagerung API does not provide the needed naturality lemma. No fake proof.

Lean: tmp/sheaf/xif/paper/S2194TransferCompatProofActual.lean
EXIT=0; SHA256 909F31956DB16B85A3155A4D964E3DC8CB035D5A5C12D8886490B2B1DD1163BC
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2194TransferCompatProofActual.olean
olean SHA256: 8AFC5CDA737F4F41BA564FC2DEB145449878D3ED8E7B2BF61FBF16FFEEA7C452
axioms: none (definitions/Prop surface only; no theorem closure).