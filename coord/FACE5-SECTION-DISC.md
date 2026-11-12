# Face 5 candidate section 2: l-division polynomial discriminant (A909)

## Formula

For the `l`-division polynomial `Psi_l` of `E/Q`, the standard shape is
`disc(Psi_l) = ± l^a * Delta^b` (rational number), equivalently per finite place
`v_p(disc(Psi_l)) = a*v_p(l) + b*v_p(Delta)`.
The Lead's candidate `(l^2-1)*v_p(Delta) + l*v_p(l)` is one possible exponent pair; the
exact `(a, b)` MUST be verified against the vendor sources (`TateMulByN`, `DivisionPolynomial`).
We did not verify it in this session and do not claim the exact exponents.

## Verdict

`disc(Psi_l)` is a rational number, hence a global function on `P^1`: its divisor is
principal and the sum of all valuations (finite + archimedean) is ZERO (product formula).
It gives a GLOBAL IDENTITY of degree 0, not a positive lower bound.  The target quantity
`V - (sF-1)*A` involves `q` and the hull volume, while the discriminant divisor involves
`Delta` and `l`; a dictionary identity between them would be required and it is not
sign-definite.  Therefore `disc(Psi_l)` does NOT provide the required nonzero section of
`H = det(hull) (x) L_q^{-(sF-1)}`: the route FAILS as a face-5 section (consistent with
chain 3's expectation that this kind of element yields an identity).

## Lean interface

`tmp/sheaf/xif/paper/Mzk1Face5DiscInterfaceActual.lean` (green):
- `DiscSectionData`, `DiscPrincipalData`;
- `principal_zero_of_DiscPrincipalData`;
- `disc_not_target_of_positive` (a positive target degree cannot equal a principal 0);
- `discRows` status table (formula TO VERIFY; verdict FAILS).

## Remaining

The real face-5 section must involve `q`/theta data (theta constants, Kummer value), not
`Delta`/`l` alone; the construction obligation `Face5ConstructionObligation` of
`Mzk1Face5ProofActual` remains open.
