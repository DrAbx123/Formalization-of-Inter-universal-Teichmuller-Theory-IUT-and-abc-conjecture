# L1-F6 STAGE1: Gaussian integral basis / chosen 5-place

Date: 2026-10-22
Owner: transport
Scope: statement-stage audit only. No production file changed.

## Files audited (read-only)

| file | lines | SHA256 |
|---|---|---|
| `LeanFormal/IUT/IUTII/Frobenioid/Example36GaussianIntegralBasis.lean` | 353 | `683D102A9A24F0F7E02551E27DF0D859C5450DCDCB3C18B00D1293B154427346` |
| `LeanFormal/IUT/IUTII/Frobenioid/Example36GaussianSplitPlaceArithmetic.lean` | 1395 | `3FABEE4B5758035B0BE37BC984A2CA8B1E66F380AB053FD5CDB74187D32D7F2E` |

Static check: no `sorry`, `admit`, `axiom`, `constant`, or `residual`
matched in either file. Build was **not** run in this statement-stage pass.

## 1. Integer-ring equivalence (complete in source)

`Example36GaussianIntegralBasis` contains:

- `gaussianRingOfIntegersEquivGaussianInt :
    NumberField.RingOfIntegers GaussianField ≃+* GaussianInt`
  via `IsIntegralClosure.equiv` (no card/refl);
- `gaussianIntEquivRingOfIntegers : GaussianInt ≃+* NumberField.RingOfIntegers GaussianField`
  (`symm` of the above);
- `gaussianRingOfIntegersEquivGaussianInt_algebraMap` and
  `gaussianIntEquivRingOfIntegers_algebraMap` (compatibility with both
  embeddings into `GaussianField`);
- `gaussianRingOfIntegersEquivGaussianInt_generator` and
  `gaussianIntEquivRingOfIntegers_sqrtd` (the chosen `i`);
- both inverse laws as `@[simp]` theorems.

Conclusion: the integral-basis/ring-of-integers gap is **closed at the
statement and proof level in this file**; no new integral-basis declaration is
needed for L1-F6.

## 2. Chosen place (uniform, not determined)

The source proves the concrete place lies over 5 and is one of the two primes:

- `concreteGaussianFivePlace_under_eq` / `concreteGaussianFivePlace_under_rational`;
- `concreteGaussianFivePlace_maximalIdeal_eq_plus_or_minus` (a disjunction);
- residue characteristic 5 and residue field equivalent to `ZMod 5`;
- relative ramification index and residue degree 1.

It does **not** determine whether the classical choice is the `(2+i)` or
`(2-i)` prime. All consumer statements are uniform in that prime; this is a
genuine non-determination, not a missing proof obligation for the uniform
theorems.

## 3. `e = 1` valuation / unit statements (present, pointwise)

The following are already proved in the consumer file:

- `concreteGaussianFivePlace_valuation_algebraMap`: for `x : ℚ`,
  `v_5(x) = v_{concreteGaussianFivePlace}(algebraMap ℚ GaussianField x)`;
- `concreteGaussianFivePlace_valuation_eq_one_iff`: pointwise
  `v_5(x) = 1 ↔ v_place(algebraMap x) = 1`;
- `concreteGaussianFivePlace_valuation_completionMap`: the same equality after
  completion, stated with `Valued.v`.

Gap: these are pointwise rational-value statements. There is no packaged
statement that the image of `ℚˣ` lands in the `v = 1` unit subgroup of the
Gaussian place. That is the smallest remaining unit-group bridge.

## 4. `concreteGaussianFivePlace` consumer status

`Example36GaussianSplitPlaceArithmetic` imports
`Example36GaussianIntegralBasis` and consumes the equivalence/valuation facts in:

- `concreteGaussianFivePlace_under_eq`;
- `concreteGaussianFivePlace_five_mem`;
- `concreteGaussianFivePlace_residueCharacteristic`;
- `concreteGaussianFivePlace_ramificationIdx_eq_one`;
- `concreteGaussianFivePlace_valuation_algebraMap`;
- `concreteGaussianFivePlace_valuation_eq_one_iff`;
- `concreteGaussianFivePlace_valuation_completionMap`.

No residual consumer theorem or placeholder provider was found in the audited
files.

## 5. Minimal next provable declaration (stage 2)

Proposed next theorem, staying inside the existing uniform-prime scope and
using only the pointwise unit statement above:

```lean
namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

theorem concreteGaussianFivePlace_rational_unit_valuation_eq_one
    (x : ℚˣ) :
    (IsDedekindDomain.HeightOneSpectrum.valuation GaussianField
      concreteGaussianFivePlace.maximalIdeal)
        (algebraMap ℚ GaussianField (x : ℚ)) = 1
```

Natural proof route:

1. `concreteGaussianFivePlace_valuation_eq_one_iff (x : ℚ)` reduces the goal to
   the 5-adic valuation of `(x : ℚ)`;
2. a unit of `ℚ` is a unit of the 5-adic valuation ring, hence has valuation 1
   (use the existing `IsDedekindDomain.HeightOneSpectrum.valuation` unit API,
   with `x` nonzero and `v_5(x) = 1`);
3. rewrite by step 1.

This declaration is minimal: it closes the only identified pointwise-to-unit
gap and does not require deciding the `(2+i)/(2-i)` choice.

## 6. Remaining risk / not claimed

- The proposed declaration is not yet written or compiled.
- A full unit-group isomorphism between `ℚˣ` and a subgroup of Gaussian units is
  **not** claimed; only the rational-unit image has valuation 1.
- No source-category G2/cocone claim is made in this document.
