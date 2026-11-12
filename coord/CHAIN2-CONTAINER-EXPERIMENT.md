# ROUTES 14 chain 2: holomorphic-structure family container (A878)

Status: local experiment NOT EXECUTED (interface/design only).  No numeric interval or
volume is asserted.  Path alpha/Brandt is retracted (see `coord/BRANDT-EXPERIMENT.md`,
which is kept as a rejection record).

## Design (ROUTES 14, chain 2)

- `h(v)`: set of holomorphic (ring) structures on the single analytic data at place v,
  with pilot valuation `ord_h`.
- `P(v,j) = union over h of (Theta value acting on the log-shell region)`.
- Global constraint `G`: the choices `(h_v)_v` must induce one global degree (Step (xii)
  rigidity).

## Judgment experiment (to be run)

1. Fix one bad place v.
2. Compute the shell volume of `P(v,j)` as a function of the allowed ord_h interval [a,b]
   (expected data: `possibleImageShellVolume : Real -> Real -> Real`).
3. Ask how narrow an interval the global constraint G enforces (`globalConstraint a b`).
4. Outcomes:
   - no G: the union is too large, the upper bound is lost (`NoConstraintTooBig`);
   - G too strong: the q-pilot member leaves the family (`ConstraintTooStrong`);
   - intermediate: the q-pilot stays and the bound survives (`MiddleAlive`) => chain 2
     survives.

## Lean interface

`tmp/sheaf/xif/paper/Mzk1Chain2ContainerInterfaceActual.lean` (status to be compiled):
- `Chain2LocalData` fields (`holomorphicStructures`, `ordH`, `possibleImageShellVolume`,
  `globalConstraint`, `qPilotOrd`);
- criteria `NoConstraintTooBig`, `ConstraintTooStrong`, `MiddleAlive`, `Chain2Survives`;
- `chain2Rows` status table (all criteria NOT evaluated).

## Conclusion

Chain 2 is at the design/interface stage: the container must be made q-dependent, and the
local volume computation plus the width of G are the two missing inputs.  No survival claim
is made.  The interface is ready for the computation (owner abc).
