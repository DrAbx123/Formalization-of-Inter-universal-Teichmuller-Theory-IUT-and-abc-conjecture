# S2113 M2b transfer: report

Date: 2026-11-02.

## Artifacts

- Lean file: tmp/sheaf/xif/paper/S2113M2bTransferActual.lean
  - SHA256: D5CED7AA6B433EE4B9461F20F273E5AD22DB985D82F6816B9E1D3F5F9B86E894
  - bytes: 22828
- Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S2113M2bTransferActual.olean
  - SHA256: F452A45090B1C3BF826619596ECA2D14A626059116D8AF6246E580714619CF39
  - bytes: 678088
- Compile command: lake env lean -o <olean> <file>
- EXIT: 0 (fresh compile, no sorry/admit, no new axiom)
- Axioms of all exposed theorems: propext, Classical.choice, Quot.sound only.

## What is proved unconditionally

1. artinTransfer_fixedField: PadicField.artin_transfer specialised to the
   fixed-field extension L_H/L_K (K' = FH H h). This is the norm side of M2b
   on the PadicField carrier.

2. localArtinTorsionEquiv_apply: the S2098 M2a torsion equivalence is the
   Artin map on roots of unity,
   localArtinTorsionEquiv U z = galoisGroupEquiv U (artin z).

3. galoisGroupMaximalAbelian_mk, galoisGroupEquiv_restrictNormalHom,
   kappa_of: the canonical map
   kappa U = galoisGroupMaximalAbelian U o abelianizationToTopological U
   computes the restriction of localGaloisGroupEquiv U k, compatibly with
   S2089's galoisGroupEquiv.

4. canonicalEquiv_apply: computation rule for the canonical levelwise
   equivalence built from the M2c carrier comparison.

5. Conditional reductions: TransferBridge (the missing comparison) gives
   CanonicalTransferCompat; M2c + TransferBridge give LocalReciprocityData,
   muQZComparison and muHatComparison, and (with an explicit identification
   of S2098's Nonempty.some with the canonical carrier) also S2098's literal
   localReciprocityData_of_source.

## Exact first missing

(A) TransferBridge: the abstract Verlagerung
    verlagerungOpen h : Ab K -> Ab H
    transported by kappa is the Galois norm/Artin transfer on roots of unity.
    There is no API in the tree comparing these two transfers.
    Defined in the Lean file as TransferBridge : Prop; not assumed.

(B) VerCarrierComparison: PadicField.ver is stated on
    K' : IntermediateField K Omega, so artinTransfer_fixedField lands in
    Gal(maxAbelian (FH H h)/FH H h), not in S2027's
    Gal(maximalAbelianExtension H / localField H). The two fields are the
    same subset of Qbar_p but carry different Algebra instances; no lemma
    identifies the two Galois groups or transports ver. Defined as
    VerCarrierComparison : Prop in the Lean file.

(C) S2098 localReciprocityTransferCompatibility hc uses (hc U).some for an
    arbitrary hc : forall U, Nonempty (...). The extracted equivalence is not
    the canonical map. The file states the exact hypothesis hcanon that
    identifies it with the canonical carrier; without it, no proof can
    control the extracted choice.

## Next executable step

Prove the group-theoretic naturality of MonoidHom.transfer under the
isomorphism localGaloisGroupEquiv K (and its restriction to H.subgroupOf K),
then combine with (B) to obtain TransferBridge. Alternatively, restate S2098's
transfer compatibility with the explicit canonical carrier
(localArtinSourceDataOfCanonical in this file) instead of Nonempty.some.
