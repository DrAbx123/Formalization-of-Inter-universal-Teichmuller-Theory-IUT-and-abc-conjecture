# TransferBridge audit: carrier side actual, naturality side missing

## Already actual (pre-existing, kernel-clean artifact)
- S2119VerCarrierActual.lean: source SHA256 1B2658757CF3E776805B50BC54C30A6C22B1A63574C1F3EF7C1B599121419DF6; olean SHA256 176D9FEDC05B33320F962BC4498548B190BE7A4FD2DF3E260DD33F3CB171FDA6.
- S2119 proves `VerCarrierComparison` unconditionally (S2113's carrier-level missing is closed): `galK'EquivLocal`, `verCarrierComparison`, `verS2027`, `artinTransfer_S2027`.
- S2113 has actual `artinTransfer_fixedField` (ported norm/transfer on fixed fields).

## What TransferBridge still needs
S2113 `TransferBridge` (line 358) is the statement:
  forall {H K} (h : H ≤ K) (v : torsion (Abelianization K)),
    torsionMap (kappa H) (torsionMap (verlagerungOpen h) v)
      = localArtinTorsionEquiv H
          (fixedFieldTorsionUnitsInclusion h
            ((localArtinTorsionEquiv K).symm (torsionMap (kappa K) v))).
S2119 only builds the carrier transport `galK'EquivLocal` and the Galois-side `verS2027`/`artinTransfer_S2027`. It explicitly leaves this abstract-vs-Galois transfer comparison as S2113's remaining item (A).

## Exact first missing
A naturality/compatibility theorem for the abstract Verlagerung under `kappa`, e.g. a proved lemma of the shape:
  torsionMap (kappa H) (torsionMap (verlagerungOpen h) v)
    = torsionMap (verS2027 h) (torsionMap (kappa K) v)
or, equivalently, an identification of `kappa` with the local Artin map on torsion (which would also need M2c for the abstract carrier). No such theorem exists in the tree; TransferBridge is not proved.

Does TransferBridge syntactically require M2c? The statement uses `kappa` (defined unconditionally) and `verlagerungOpen`; M2c is not a hypothesis of the definition. However the only clear route to compare the abstract transfer with the Galois transfer goes through the canonical carrier comparison `canonicalTorsionComparison`, i.e. M2c. So: no syntactic dependency is asserted, but no M2c-free proof was found; the exact missing lemma above is independent of that question.

## heq / EndComm
Still missing: S2159/S2131 action-equivariance `heq`, comparing the muQZ action with PsiCnsCoefficientAction. It is not implied by TransferBridge alone. Exact chain:
  M2cFirstMissing -> canonicalTorsionComparison -> S2048 LocalArtinTorsionMap
  + TransferBridge -> ArtinTransferCompat -> LocalReciprocityData -> muHatComparison
  + heq -> S2432EndComm -> literal S2189.

## Status
No new Lean file was compiled; no build/cache command. Carrier comparison actual is S2119; TransferBridge/heq remain exact missing; no fake/conditional input labeled actual.