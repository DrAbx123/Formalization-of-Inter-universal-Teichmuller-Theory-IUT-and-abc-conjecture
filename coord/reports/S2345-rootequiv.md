# S2345: roots in O_L versus roots in L

Date: 2026-11-03. Layer O; consumer S2342/S2217.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2345RootSetEquivActual.lean
  SHA256 2F548D8956E1522A751FFCFA5983978669E4806FE65ED0AA521CA78DC53B22AC
  EXIT=0
  olean SHA256 25FAB90E0E3F0EF11DF9F695A141074AD64A31EC46B078CD5E9E87A37EF3BD0C
  size 151648
  axioms propext, Classical.choice, Quot.sound.

Definitions/theorems:

- s2345P f = f.map (algebraMap O_K K);
- s2345ToFun f hmonic:
    f.rootSet (RingOfIntegers L) -> (s2345P f).rootSet L,
    alpha |-> algebraMap O_L L alpha;
- s2345ToFun_bijective:
    injective by RingOfIntegers.coe_injective;
    surjective by IsIntegralClosure.isIntegral_iff: any root in L is integral
    over O_K (root of monic f), hence comes from O_L; then use
    aeval_algebraMap_apply to show the lift is a root;
- s2345RootSetEquiv:
    f.rootSet (O_L) ~= (s2345P f).rootSet L;
- s2345RootSetEquiv_apply:
    the equivalence commutes with algebraMap O_L L by definition.

## Exact first missing: Galois action compatibility

The equivalence is compatible with algebraMap, but compatibility with the
Gal(L/K)-actions is not yet stated/proved.  The root set in L has the
Polynomial.Gal action used by S2167 rootPerm; the O_L root set needs an
explicit Galois action (via MulSemiringAction on O_L) and one must prove

  s2345RootSetEquiv (sigma • alpha) = sigma • s2345RootSetEquiv alpha.

After that, the arithFrobAt reduction compatibility from S2342 step 2 remains.

## Conclusion

- BUILT: actual O_L/L root-set equivalence and algebraMap compatibility.
- MISSING: Galois action compatibility, then arithFrobAt compatibility and
  factor multiset identification.
- no fake; no false S2057 data.
