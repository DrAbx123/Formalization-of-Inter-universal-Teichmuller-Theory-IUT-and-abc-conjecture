# S2442 / S2048: M2a/M2b actual-construction audit

## Actual baseline (kernel-clean, no change)
- tmp/sheaf/xif/paper/S2442MuQZFinalActual.lean
  - EXIT=0; source SHA256 D290C70F48BBA29CE068982CC345BF2A4FEC572A2F564B2AB847A489A93BDA6E
  - olean SHA256 6FC270E7C19947E6943EEAFDB72CF8528E41A3386CAC116DB6F205089A20CB95
  - axioms propext, Classical.choice, Quot.sound.
  - corrected g^-1-indexed data, action, g^-1 action_compat, anti-hom, inverse laws, per-g discrete continuity, muHat action.

## (1) S2048 LocalArtinTorsionMap r: NOT constructible actual yet
S2048 needs a field `artin : forall U, mu p U ≃* torsion (Abelianization U)`.
S2102TorsionArtinActual provides the actual Artin torsion equivalence only at the profinite carrier:
  localArtinTorsionEquiv U : mu p U ≃* torsion (Gal(maxAb/L_U)).
S2048 needs the abstract abelianization carrier `torsion (Abelianization U)`. The bridge is exactly S2109's M2c:
  canonicalTorsionComparison p U : Nonempty
    (torsion (Abelianization U) ≃* torsion (TopologicalAbelianization (localGaloisGroup p U))).
S2109 proves this conditionally on `CommutatorClosed U`, and records the exact missing:
  M2cFirstMissing : forall U, CommutatorClosed U
(S2117 reduces it further to `PadicAbsoluteGaloisTopologicallyFinitelyGenerated` + Nikolov-Segal commutator width; those remain named inputs).
Therefore S2048's LocalArtinTorsionMap is blocked by M2cFirstMissing; no inhabitant was constructed.

## (2) ArtinTransferCompat p r: NOT constructible actual yet
S2113M2bTransferActual supplies the actual ported norm/transfer theorem:
  artinTransfer_fixedField {H K} (h : H ≤ K) (y : mu p K).
The remaining square, however, needs the carrier bridge and is isolated there as:
  TransferBridge : Prop  (Ver o kappa = localArtinTorsionEquiv o fixedFieldTorsionUnitsInclusion o localArtinTorsionEquiv.symm o kappa).
S2113 proves `CanonicalTransferCompat` from `TransferBridge` unconditionally, and derives S2024/S2017 data from M2c + TransferBridge:
  localReciprocityData_of_canonical, muQZComparison_of_canonical, muHatComparison_of_canonical.
Thus ArtinTransferCompat needs M2c + TransferBridge; neither is actual in the tree.

## (3) action-equivariant muHatComparison / EndComm
Even after M2c + TransferBridge, `muHatComparison` only gives a multiplicative equivalence; action equivariance requires the S2159/S2131 `heq` field comparing the muQZ action with PsiCnsCoefficientAction. That field is not present. Exact missing chain:
  M2cFirstMissing (all U)
  -> TransferBridge
  -> LocalReciprocityData -> muHatComparison
  -> S2159/S2131 action-equivariant module comparison
  -> S2432EndComm
  -> literal S2189MuQZMulAutData.
No stage was faked or assumed.

## Exact first missing, dependency order
1. M2cFirstMissing : forall U, CommutatorClosed U (S2109), or equivalent torsion criteria;
2. TransferBridge (S2113);
3. S2159/S2131 action-equivariant comparison heq (action of Gv on the two cyclotomes);
4. then S2432EndComm and literal S2189.
Joint continuity remains S2442JointContinuityRequired(T) for a declared topology T; per-g discrete continuity is actual.

## Artifacts
S2442 actual remains the last kernel-clean integration. No new Lean file was compiled for this audit; no build/cache command used.