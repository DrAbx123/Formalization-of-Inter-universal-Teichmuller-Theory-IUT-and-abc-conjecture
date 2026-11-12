# kappa / Verlagerung naturality: audit and exact missing

## Actual pre-existing
- S2119VerCarrierActual.lean: carrier side of M2b is closed; `verCarrierComparison`, `verS2027`, `artinTransfer_S2027` actual (source SHA 1B2658757CF3E776805B50BC54C30A6C22B1A63574C1F3EF7C1B599121419DF6; olean SHA 176D9FEDC05B33320F962BC4498548B190BE7A4FD2DF3E260DD33F3CB171FDA6).
- S2113M2bTransferActual.lean: actual `artinTransfer_fixedField` and the definition of `TransferBridge`; it also proves `CanonicalTransferCompat` from `TransferBridge`.
- S2017: actual `verlagerungOpen`; S2089/S2102: actual local Artin torsion equivalence.

## Exact missing naturality statement
For H <= K and v : torsion (Abelianization K), the required square is:
  torsionMap (kappa H) (torsionMap (verlagerungOpen h) v)
    = torsionMap (verS2027 h) (torsionMap (kappa K) v),
where `kappa U : Abelianization U ->* Gal(maxAb U / L_U)` is S2113's canonical quotient map (topological abelianization followed by galoisGroupMaximalAbelian), and `verS2027 h` is S2119's transported PadicField.ver.
Equivalently, a `kappa`-identification on torsion: `kappa` transported along `localArtinTorsionEquiv` should be the local Artin transfer.
No theorem of this shape exists in the tree. The S2119 computation only identifies the Galois-side carrier and `PadicField.ver`; it does not relate the abstract `verlagerungOpen` to `verS2027` under `kappa`.

## M2c dependence
- The statement itself does not mention `canonicalTorsionComparison`; syntactically it is M2c-free.
- No M2c-free proof was found. The natural proof route goes through the canonical carrier comparison `canonicalTorsionComparison` (M2c): replace `torsion (Abelianization U)` by `torsion (TopologicalAbelianization G_U)`, identify `kappa` with the canonical map, then use S2119's `artinTransfer_S2027` and the actual ported norm theorem.
- Therefore the exact dependency is: naturality lemma is the missing bridge; if proved via carriers it consumes M2cFirstMissing, but the implication itself is not established. No claim of an M2c-free proof is made.

## Downstream
TransferBridge = this naturality plus the S2119 carrier transport. It is not proved.
heq (S2159/S2131 action equivariance) is still a separate missing field.

## Status
No new Lean file compiled; no build/cache command. No fake/conditional data labeled actual. The concrete first missing is the `kappa`-naturality lemma above (or an equivalent identification of kappa with local Artin transfer on torsion).