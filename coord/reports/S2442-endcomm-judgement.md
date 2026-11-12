# S2442 EndComm final status (updated)

## Actual (kernel-clean)
File tmp/sheaf/xif/paper/S2442MuQZFinalActual.lean
- EXIT=0; source SHA256 D290C70F48BBA29CE068982CC345BF2A4FEC572A2F564B2AB847A489A93BDA6E
- olean SHA256 6FC270E7C19947E6943EEAFDB72CF8528E41A3386CAC116DB6F205089A20CB95
- axioms propext, Classical.choice, Quot.sound; no sorryAx.
- Corrected g^-1-indexed S2442MuQZMulAutData_actual, action, g^-1 action_compat, anti-hom A_g.comp A_h=A_(h*g), inverse laws, per-g discrete continuity, muHat action.
Dependency S2432MuQZMulAutDoneActual.lean EXIT=0; source SHA 936E739FB51D6B1FA17FED0827373B1D6AE129ED82A54DBF9796C7E700ACAE5B; olean SHA C1213072E22A63431305A477A080FA5EDB6E42CD37218AB2DA49E233CBF275D8.

## S2432EndComm: undecided, not refuted
Literal g-indexed S2189 is equivalent to S2432EndComm:
  S2442S2189Literal_iff_EndComm : Nonempty (S2189MuQZMulAutData p) <-> S2432EndComm.
No transfer-only proof and no counterexample were obtained after the anti-hom law was established.

## Exact first missing (most useful concrete form)
S2048TransferCompatActual provides the cleanest reduction:
- LocalArtinTorsionMap p (S2048 line 131),
- ArtinTransferCompat p r (S2048 line 151),
- localReciprocityDataOfArtin (r) (hc) : LocalReciprocityData p,
- muHatComparison_of_data / muHatComparison_of_source.
Thus an actual action-equivariant muHatComparison can be built if one supplies a genuine LocalArtinTorsionMap r together with ArtinTransferCompat p r (equivalently the local reciprocity transfer square), and then proves that this comparison intertwines the muQZ action with PsiCnsCoefficientAction. The latter action equivariance is exactly the S2159/S2131 heq field; it is not present in the tree.
No unconditional muHatComparison and no EndComm are claimed.

## Joint continuity
S2442JointContinuityRequired (T : TopologicalSpace (muQZ p)) remains the exact surface.
Per-g continuity for the S2159 discrete topology is actual; joint continuity is not proved. For an arbitrary non-discrete/profinite T, no topology is declared, so the statement is not instantiable. Exact missing: declared T plus stabilizer-open/local-constancy proof.