# S731 memo: Ehrhart / lattice polytopes / toric geometry vs paper Θ hull log

Date: 2026-10-30
Status: research memo. No Lean theorem claimed. No fake construction.

## 0. Target and the actual formal shape

The current paper object is the per-b paper-coefficient root theta hull:

```lean
paperRootThetaHull T b : Set (qVFamTensorBlock T b)
```

where

```lean
qVFamTensorBlock T b =
  ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple
```

and, by `RootHullContainmentInequalityActual`,

```lean
rootThetaRegion j =
  (arithmeticTupleFractionalLattice places tuple
      (fun i => (gaussExponent j.1).toNat * cRoot i) *
    arithmeticTupleHolomorphicLattice places tuple : Set _)

rootThetaHull = closure (⋃ j, rootThetaRegion j)
```

The desired paper log is

```lean
paperRootThetaHullLog T b mu =
  rootThetaHullLog ... mu (paperRootCoefficientFamily T b)
```

with the exact remaining formula gap

```lean
PaperRootHullFormulaGap T b
  -- data : ArithmeticTuplePureFractionalScalingData ... paperRootCoefficientFamily
  -- hull_eq : paperRootThetaHull T b =
  --   fractionalLattice * holomorphicLattice
```

and formula

```lean
paperRootThetaFormulaLog T b =
  -((∑ _ : qVFamTensorV, qVFamPaperRootCoefficient T b) *
      Real.log (qVFamTensorP T b : Real))
```

Thus the target scalar is a **p-adic normalized Haar log of a fractional
`Z_p`-lattice region**, once the hull equality is supplied.

## 1. Is the paper hull a rational / lattice polytope?

No. The actual object is:

* a finite-dimensional p-adic vector space `FinitePadicTensor`;
* `arithmeticTupleFractionalLattice places tuple c` is a `Z_p`-submodule
  (fractional lattice), not a bounded real or rational polytope;
* `arithmeticTupleHolomorphicLattice` is the integral closure/lattice, not a
  set of vertices;
* `rootThetaHull` is the closure of a union of such lattice-scaled regions.

There is no vertex set, no polyhedral inequality description, and no
`t`-scaling parameter. `RootHullClosednessActual` also records that even the
equality of the root hull with the minimal fractional-lattice region is not
available unconditionally (that file is marked unnecessary for the current
target, but it confirms there is no proven polyhedral hull equality).

Therefore Ehrhart theory has no input polytope. A rational polytope would
require a finite vertex set and an ambient real vector space with lattice;
`qVFamTensorBlock` is a p-adic tensor block and its regions are lattices.

## 2. Ehrhart counts vs Haar log

Ehrhart theory applies to a rational polytope `P ⊂ R^d` and a lattice `L`:

```text
L_P(t) = #(tP ∩ L)
```

for integer `t`; for rational `P` this is a quasi-polynomial with leading
coefficient `vol(P) / covol(L)`.

The paper target is not `#(tP ∩ L)`. It is the Haar measure, relative to the
canonical unit, of a fixed compact open lattice region:

```text
Haar(F(c) * O_hol) = p^{-∑ c_i}
log of normalized Haar = -(∑ c_i) log p
```

(one-factor/rank-d versions: `p^{-d c}`, `-d c log p`). There is no Ehrhart
variable `t`; the hull is not scaled by an integer parameter. Adding an
artificial scaling `t` multiplies the Haar by `t^d` and adds `d log t`, which
is not the Ehrhart count.

Concrete sympy probe (run 2026-10-30, sympy 1.14.0):

```text
p = 5, c = 1/2
rank 1: Haar = sqrt(5)/5,  log = -log(5)/2
rank 2: Haar = 1/5,        log = -log(5)

Ehrhart interval [0,N]: N*t + 1,       leading coeff N
Ehrhart square [0,N]^2: N^2*t^2 + 2N*t + 1, leading coeff N^2

Haar log rank1: -log(5)/2
Haar log rank2: -log(5)
t copies rank1 log: log(t) - log(5)/2
Ehrhart t interval: N*t + 1
```

The Haar log and the Ehrhart leading term are different invariants and have
opposite dependence on the lattice index (Haar is reciprocal covolume; Ehrhart
leading coefficient is covolume).

## 3. Toric geometry

Toric geometry could compute a moment polytope / Newton polytope only if:

* the Θ hull carried a torus action with a moment map, or
* the Θ divisor/line bundle had a toric model whose Newton polytope computes
  its volume.

The paper Θ-pilot hull does not have a torus action: the finite symmetry is the
`mu_{2l}` root ambiguity / finite label group, not a split torus; the hull is a
p-adic lattice region, not a complex toric variety. The root stack is the
finite extension `L = K(root)` (`rootNormedExtension`), not a toric stack.
There is no moment polytope or Newton polytope available for the target.

Verdict: toric geometry does not apply.

## 4. Quasi-polynomial / lattice-point counts

Even if one modeled a finite truncation of the hull as a rational polytope,
Ehrhart/quasi-polynomial would give an asymptotic lattice-point count, not the
paper normalized log-volume. The paper normalization is by the canonical unit
reference / holomorphic lattice, and the exact formula is the fractional-lattice
index formula already used in
`arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic`:

```lean
arithmeticTupleNormalizedLogVolume ... (fractionalLattice c * holomorphicLattice)
  = -((∑ c_i) * Real.log p)
```

This is the actual computation route; Ehrhart adds no theorem and cannot fill
`PaperRootHullFormulaGap`.

## 5. Exact minimal bridge if one insists

A paper-faithful Ehrhart route would need all of:

1. a rational polytope `P` and lattice `L` with a proved equality
   `paperRootThetaHull T b = (P ∩ L) * O_hol` (or a fundamental-domain
   description);
2. a proof that the Haar normalization of `P ∩ L` equals the Ehrhart leading
   term/covolume, including the canonical unit normalization;
3. a proof that this equals `paperRootThetaFormulaLog T b`.

Items 1–3 are not in the repo, and item 1 is false for the current lattice
module as stated (a `Z_p`-lattice is not a bounded polytope). The only actual
formula remains the fractional-lattice Haar index formula conditional on
`PaperRootHullFormulaGap`.

## 6. Verdict

| Question | Answer |
|---|---|
| Is paper Θ hull a rational/lattice polytope? | **No**; it is a closure of fractional `Z_p`-lattice regions. |
| Does Ehrhart/quasi-polynomial compute the paper log? | **No**; Ehrhart counts lattice points / leading volume, paper target is fixed Haar log. |
| Does toric geometry apply? | **No**; no torus action/moment polytope for the p-adic Θ hull. |
| Can it fill `PaperRootHullFormulaGap`? | **No.** |
| Correct actual route | fractional-lattice Haar index formula, conditional on the existing exact hull equality gap. |

No fake hull, no fake polynomial, no target change.
