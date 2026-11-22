# S1932: geometric core of the sign action of the actual S1726 orbicurve; exact remaining missing

File: `tmp/sheaf/xif/paper/S1932SignActionQuotientActual.lean`

- EXIT = 0 (`lake env lean -j1 -R D:/lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1932SignActionQuotientActual.olean tmp/sheaf/xif/paper/S1932SignActionQuotientActual.lean`)
- olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1932SignActionQuotientActual.olean` (234824 bytes)
- SHA256(source) = `91F7060AE32774175C496D8E40C06274639105DAEED2A157F8BDEB676A337A2A` (13005 bytes, 256 lines)
- axioms: every `#print axioms` in the file reports only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`/`admit`, no new axiom.

## Constructed (genuine, no postulate)

1. `S1932AffineEndo_comp : S1898AffineEndo ; S1898AffineEndo = 1` -- the actual
   `[-1]` coordinate endomorphism `(x, y) |-> (x, -y)` of the affine Weierstrass
   model of E' over F' is an involution.  Chain:
   `S1932PolyEndo_comp` (polynomial ring), `S1932CoordEndo_comp` (coordinate ring
   `R' = F'[x,y]/(y^2 - x^3 - a2 x^2 - a4 x)`, via `Ideal.Quotient.mk_surjective`),
   `S1932SchemeEndo_comp` (`Spec`), `S1932AffineEndo_comp` (the `Over (Spec F')`
   endomorphism).
2. `S1932SigmaSqIso : Sigma ; Sigma ~= 1` for the actual 2-Yoneda lift
   `S1932Sigma = S1898EllipticInvolutionHom` of S1898: the `U`-component sends a
   scheme point `P` to `(P ; [-1]) ; [-1] = P`; constructed as a modification
   (`S1932SqMod` / `S1932SqModRev`, `Iso.mk`).  This is the only non-trivial
   coherence datum of the sign action.
3. The subsingleton machinery that makes the remaining pseudofunctor coherences
   automatic: `S1932NatTransSubsingleton`, `S1932CatHom2Subsingleton`,
   `S1932StrongTransSubsingleton` (every 2-cell between endomorphisms of the
   representable S1726 stack lives in a discrete category).

## Exact remaining missing

`S1932SignActionMissing l` = existence of `A : Iut.OrbicurveSignAction S1726Orbicurve`
with `A.inversion = S1898EllipticInvolution l`.  What is still missing there is the
Lean assembly of the pseudofunctor `SignActionIndex -> EtaleStackPseudofunctor F'`
(the three trivial `mapComp` unitor isomorphisms `1;f ~= f`, `f;1 ~= f`, `1;1 ~= 1`);
the `(Sigma,Sigma)` case IS `S1932SigmaSqIso`, and all remaining coherence equations
are `Subsingleton.elim` by item 3.  So the mathematics of the action is complete;
the gap is the unitor plumbing of the pseudofunctor bicategory.

`S1932CFQuotient l A` = the paper's quotient `C_F = X_F/{+-1}` for a sign action `A`:
`cF : Iut.HyperbolicOrbicurve (S1732A l).F` with `cF.signature = (1,1)^pm`,
`quotient : Iut.OrbicurveSignInvariantMorphism A cF`, and
`quotientWitness : Iut.OrbicurveSignQuotientWitness A quotient`.

`S1932PaperCF_iff` proves `Nonempty (S1886PaperCF l) <-> exists A, Nonempty (S1932CFQuotient l A)`,
and `S1932PaperCF_of_data` builds `S1886PaperCF` from any action + quotient datum.
The quotient stack `[X_F/{+-1}]` is not in the tree (no stackification of groupoid
actions), so it is neither constructed nor postulated; the signature-relabeling
object of S1886 is explicitly not used.

## Important finding for the lead

`S1886PaperCF` does not tie `action.inversion` to `S1898EllipticInvolution`: it
quantifies an arbitrary `OrbicurveSignAction` on `S1726Orbicurve`.  So
`S1932PaperCF_iff` is stated with the action unconstrained; the stronger target
`A.inversion = S1898EllipticInvolution l` is recorded separately as
`S1932SignActionMissing`.  Consumers that want the actual geometric action must add
that constraint (or use the S1898 lift directly).

## Compile status

- `statement_compiles`: yes (EXIT 0)
- `proof_body_checked`: yes
- `kernel_closed`: yes for every declaration in the file
- `target_accepted`: action packaging NOT closed (first missing = diagram unitors);
  quotient NOT closed (stated exactly); the geometric involution and
  `Sigma ; Sigma ~= 1` are closed and reusable.
