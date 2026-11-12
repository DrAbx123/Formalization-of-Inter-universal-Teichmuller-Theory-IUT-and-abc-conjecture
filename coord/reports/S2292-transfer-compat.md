# S2292: actual transfer naturality lemmas

Layer: O (transfer compatibility).
Source object: transferAb, transported transversals.
Domain: transfer under conjugation.
Direction: actual map_diff, transport_smul, transferAb_natural; verlagerungOpen/toStage specialization remains.

BUILT:
- S2292_map_diff: ψ(diff ϕ S T) = diff (ψ.comp ϕ) S T.
- S2292_transport_smul: transport(g • S) = (e g) • transport(S).
- S2292_transferAb_natural: Abelianization.map eH(transferAb_H(of g)) = transferAb_H'(of(e g)).

PROVED: transferAb naturality; axioms trio.

MISSING: specialize to verlagerungOpen (subgroup inclusion) and toStage/torsion; then S2179TransferCompatible and colimit MulAut. No fake.

Lean: tmp/sheaf/xif/paper/S2292TransferCompatActual.lean
EXIT=0; SHA256 6F16945371240EAE6374F213F0F95D1BE5D2D249FA2A4F21BF7D1C7A0ED67365
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2292TransferCompatActual.olean
olean SHA256: D9CC64D7D4234F2D0290CDCAE7E310C0891CC41F426630D140EC264F70DACA1B
axioms: propext, Classical.choice, Quot.sound (no sorryAx).