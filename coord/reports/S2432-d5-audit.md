# S2432 (D5): compile-gate audit and exact missing

Date: 2026-11-03.

## Gate results

CLEAN / EXIT=0:

1) tmp/sheaf/xif/paper/S2420DedekindApplyActual.lean
   SHA256 26F53AF2BE29DD0AA0DF26D5D67B43E2F609057BE2CD3987A388B8DCB2AE4393
   olean SHA256 388DDEBDE81F1AFA4542A616D44C175F3C3DDF9BF626CBD9679FFDF66D054EFE
   size 86048
   s2420_minpoly_frobBar, s2420RootFactor_permBar: axioms trio only.

2) tmp/sheaf/xif/paper/S2425PermBarInvarianceActual.lean
   SHA256 170F312521AAAD51DAAD0DB7B9EFBAC7245338106D624683C570FB0BA572854E
   olean SHA256 9476B00F7FD1C7816A68F6456FE94399F13236CBF221BD4527C606C057F1F4D0
   size 82648
   s2425_minpoly_frobBar, s2425RootFactor_permBar: axioms trio only.

3) tmp/sheaf/xif/paper/S2428FilterBridgeActual.lean
   SHA256 487D12CE98D6186F8FB8CF212B9888C476FD715685415F18EAFA780135A1D311
   olean SHA256 0DE405A566CEB875A110D0F24BEB37E30112F7FA0717DEF6547687820A49DA7B
   size 127608
   s2428_filter_two_le_map, s2428_filter_fiberSizes_eq_factorDegrees_filter:
   axioms propext, Classical.choice, Quot.sound; no sorryAx.

BROKEN / EXIT=1:

tmp/sheaf/xif/paper/S2427RootPermCycleActual.lean
  EXIT=1.  Theorems
    s2427RootPermBar_agrees_rootPerm
    s2427RootPermBar_eq_permCongr_rootPerm
    s2427RootPermBar_cycleType_rootCycleType
    s2427_permBar_cycleType_eq_rootCycleType
  have sorryAx in #print axioms.  DO NOT USE.  D5 is NOT accepted.

Also broken: attempts at s2427_cycleType_conj / s2427_cycleType_permCongr'
(invalid `Equiv.cycleType` projection) and a clean copy S2431
(EXIT=1, see exact missing below).

## Exact first missing

S2427/rootPerm alignment fails at a type-correctness/cast boundary:

- `s2345RootSetEquiv f hmonic` has codomain
    `(s2345P f).rootSet L`,
  while `rootPerm K L f hsplit σ` has domain
    `(f.map (algebraMap O_K K)).rootSet L`.
  `s2345P f` is definitionally this map, but after tactic rewriting the term is
  rejected under the `instances` transparency level.  Need a helper equality of
  root sets or a `change`/cast before applying rootPerm.

- In `s2427RootPermBar_agrees_rootPerm`, the subtype proof for `σ • a.1` was
  taken from `e.symm(...)`; the equality of subtype values is
  `s2368_rootTransport`, but the `Subtype.ext` term needs the root membership
  proof for `σ • a.1` first.  This is fixable with a `let xroot` + `by` proof,
  which was attempted in S2431 but then the `rootPerm` cast blocked it.

- In `s2427RootPermBar_eq_permCongr_rootPerm`, after `Equiv.permCongr_apply`
  the goal contains `(s2345RootSetEquiv ...).symm.symm a`; `rw [Equiv.symm_symm]`
  then `apply e.injective; rw [Equiv.apply_symm_apply]` is needed, not the
  previous rewriting direction.

- The final theorem `s2427_permBar_cycleType_eq_rootCycleType` must take
  `(hmonic : f.Monic) (hsep : (fbar f p).Separable)` explicitly; they do not
  occur in its statement otherwise.

## What can be integrated now

Clean, usable: minpoly/Frobenius invariance, root-to-factor map invariance,
filter bridge, and (from S2408/S2397) fibre size = natDegree and
factorDegrees multiset identity.

Missing for D5 corrected theorem: a sorry-free rootPerm/permBar cycle-type
alignment.  Without it, S2217Missing / corrected Dedekind-Frobenius is not
claimed.

## Conclusion

- S2420, S2425, S2428 are clean and queued.
- S2427 is not accepted; sorryAx present.
- D5 corrected theorem remains missing; exact blocker is the rootPerm cast
  and the final assembly.
- no fake; no false S2057 data.
