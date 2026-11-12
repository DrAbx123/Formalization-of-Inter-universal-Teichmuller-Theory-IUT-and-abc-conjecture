# M2c / TransferBridge / heq: exact audit (no fake)

## Baseline actual unchanged
- tmp/sheaf/xif/paper/S2442MuQZFinalActual.lean: EXIT=0; source SHA256 D290C70F48BBA29CE068982CC345BF2A4FEC572A2F564B2AB847A489A93BDA6E; olean SHA256 6FC270E7C19947E6943EEAFDB72CF8528E41A3386CAC116DB6F205089A20CB95; axioms propext, Classical.choice, Quot.sound.
- Corrected g^-1-indexed data, action, g^-1 action_compat, anti-hom, inverse laws, per-g discrete continuity, muHat action.
No new Lean file was compiled for this audit; no build/cache command was run.

## (1) M2c: `∀ U, CommutatorClosed U` not proved/refuted
Exact reduction already in the tree:
- S2116 `TopologicallyFinitelyGenerated U` (line 346) and `NikolovSegalCommutatorWidth` (line 359), both `Prop`, no inhabitant.
- S2116 `m2cFirstMissing_of_nikolovSegal (hNS) (hfg) : M2cFirstMissing` is a genuine implication.
- S2117 `PadicAbsoluteGaloisTopologicallyFinitelyGenerated` (line 291) is the single missing finite-generation theorem; `topologicallyFinitelyGenerated_of_padicAbsoluteGalois` reduces all U to it.
- S2117 `m2cFirstMissing_of_padicTopFG_and_nikolovSegal (hNS) (hQp) : M2cFirstMissing` is the exact actual consumer.
- Then S2109 `canonicalTorsionComparison_of_commutatorClosed` and S2113 `canonicalEquiv` give the requested `mu p U ≃* torsion (Abelianization U)` once M2c holds.
Exact first missing: the two deep inputs
  PadicAbsoluteGaloisTopologicallyFinitelyGenerated
  NikolovSegalCommutatorWidth
No proof or counterexample was obtained; no inhabitant is constructed.

## (2) TransferBridge: not constructed
S2113 has actual `artinTransfer_fixedField {H K} (h : H ≤ K) (y : mu p K)`, the ported norm/transfer theorem.
The remaining square is the named `TransferBridge` (S2113 line 358):
  forall h v, kappa H (Ver (v)) = localArtinTorsionEquiv H (fixedFieldInclusion ((localArtinTorsionEquiv K).symm (kappa K v))).
S2113 proves `CanonicalTransferCompat` from `TransferBridge`, and `localReciprocityData_of_canonical`/`muHatComparison_of_canonical` from M2c + TransferBridge.
Exact first missing: actual proof of `TransferBridge` (carrier-level comparison of the Verlagerung with norm/Artin transfer). No fake inhabitant was introduced.

## (3) heq / action-equivariant muHatComparison / EndComm
`muHatComparison` only gives a multiplicative equivalence. To derive
  S2432EndComm : forall g h, A_(g*h)=A_(h*g)
one still needs the S2159/S2131 action-equivariance `heq`: the comparison must intertwine the muQZ action with PsiCnsCoefficientAction (cyclotomic Gv-action). That field is not present.
S2442 `S2442S2189Literal_iff_EndComm` isolates literal S2189 as equivalent to S2432EndComm; no unconditional construction or refutation exists.
Exact first missing chain:
  PadicAbsoluteGaloisTopologicallyFinitelyGenerated
  -> NikolovSegalCommutatorWidth
  -> M2cFirstMissing
  -> TransferBridge
  -> S2159/S2131 heq (action equivariance)
  -> S2432EndComm
  -> literal S2189MuQZMulAutData.

## Joint continuity
S2442JointContinuityRequired (T : TopologicalSpace (muQZ p)) remains exact. Per-g discrete continuity actual; joint continuity and non-discrete T are missing (no declared topology).

## Status
No actual M2c input, no TransferBridge, no heq/EndComm, no literal S2189. No fake/conditional data labeled actual. Baseline S2442 actual remains unchanged.