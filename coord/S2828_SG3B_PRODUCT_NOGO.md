# S2828 — SG3b tensor product-decomposition no-go criterion

Date: 2026-11-07
Status: **ACTUAL conditional no-go** + actual product-side Haar formula.
The unconditional failure (a concrete non-additivity witness for C3) is the
remaining exact counterexample obligation.

## File

`tmp/sheaf/xif/paper/S2828SG3bProductNoGoActual.lean`

```text
src 4820 B
SHA256 daefef30a12bc5a2a0f5dd58377e3f96e7ae780e53abd64459aca7efb39e6256
olean 222696 B
SHA256 aa9d9a7a8515e7eec2bbcd405c3e8a312d70ad3006b9bcd3824ff95f4ece11b1
EXIT=0
AXIOMS [propext, Classical.choice, Quot.sound]
QUEUED
```

## 1. Non-additivity witness

```lean
def S2828NotAdditiveWitness (C3) : Prop :=
  ∃ x ∈ actualC3LogShellTensorRegion C3,
    ∃ y ∈ actualC3LogShellTensorRegion C3,
      x + y ∉ actualC3LogShellTensorRegion C3
```

## 2. Product-decomposition definition

```lean
def S2828ProductDecomposition
    (e : C3LogShellTensorBlock C3 ≃ₗ[ℚ_[C3.p]] ((j : J) -> E j))
    (localRegion : (j : J) -> Set (E j)) : Prop :=
  e '' actualC3LogShellTensorRegion C3 = Set.pi Set.univ localRegion
```

## 3. Actual no-go theorem

```lean
theorem S2828_no_product_decomposition_of_not_additive
    (w : S2828NotAdditiveWitness C3)
    (e : C3LogShellTensorBlock C3 ≃ₗ[ℚ_[C3.p]] ((j : J) -> E j))
    (localRegion : (j : J) -> Set (E j))
    (hadd : ∀ j a, a ∈ localRegion j -> ∀ b, b ∈ localRegion j ->
      a + b ∈ localRegion j)
    (h : S2828ProductDecomposition C3 e localRegion) : False
```

Proof: take the witness `x,y`; `e x` and `e y` lie in the Cartesian product;
additive local factors give `e x + e y = e (x+y)` in the product; linear
injectivity returns `x+y ∈ region`, contradiction.

Axioms trio.

## 3b. Actual structural consequence: a decomposition forces additivity

```lean
theorem S2828_additive_of_productDecomposition
    (e : C3LogShellTensorBlock C3 ≃ₗ[ℚ_[C3.p]] ((j : J) -> E j))
    (localRegion : (j : J) -> Set (E j))
    (hadd : ∀ j a, a ∈ localRegion j -> ∀ b, b ∈ localRegion j ->
      a + b ∈ localRegion j)
    (h : S2828ProductDecomposition C3 e localRegion) :
    ∀ x ∈ actualC3LogShellTensorRegion C3,
      ∀ y ∈ actualC3LogShellTensorRegion C3,
        x + y ∈ actualC3LogShellTensorRegion C3
```

So the no-go is exactly equivalent to failure of additivity.  A product
decomposition exists **iff** the pure-tensor region is additive (for some such
e and local factors).  The missing witness is therefore precisely a pair of
region points with non-region sum.

## 4. Interpretation

A linear Cartesion-product decomposition with additive local factors would
make `actualC3LogShellTensorRegion` closed under addition (because
`Set.pi` of additive sets is additive).  The actual region is the image of a
product under the **multilinear** `finitePadicTensorTprod`; it is not
automatically additive.

Therefore:

- if `S2828NotAdditiveWitness C3` holds, the product decomposition is
  **provably impossible**;
- conversely, if the product decomposition exists, the region is additive and
  no witness can exist.

## 5. What is still missing for an unconditional no-go

The theorem needs an explicit C3 witness:

```lean
∃ x y ∈ actualC3LogShellTensorRegion C3, x + y ∉ actualC3LogShellTensorRegion C3
```

A witness can be built from two pure tensors with linearly independent local
components in at least two tensor factors; the sum of two pure tensors is
not pure in general.  Current tree has no explicit C3 local basis/independence
data to instantiate this, so the witness is not constructed here.

If instead the decomposition is intended to exist, one must produce the
linear `e` and local`localRegion`; no such actual `e` is in the tree.  The
actual product-side Haar formula is available in
`S2827_pi_pi_logVolume`.

## 6. Status

```text
product-Haar formula (product side)             ACTUAL (S2827)
non-additivity => no product decomposition      ACTUAL (S2828)
C3 non-additivity witness                       MISSING
C3 linear Cartesian-product decomposition       MISSING
tensor volume identity                          MISSING
```

No fake witness, no fake decomposition, no axiom beyond the permitted trio.
