/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/

import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionField
import LeanFormal.IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity

/-!
# Consumer wiring of the torsion bridge into the division-field finiteness API

`IUT.ABCBridge.Galois.EllipticDivisionField` exposes the coordinate fields `K(Q)` and
`K(P i : i)` of points on a base-changed Weierstrass curve, and proves their
finite-dimensionality (and the resulting Galois-closure and Krull-topology statements)
under the hypothesis `HasIntegralCoordinates` on the coordinates.  This file is the
compiled consumer that replaces that hypothesis, for odd `n` with `(n : K) ≠ 0`, by the
named bridge interface `DivisionPolynomialDetectsTorsion (E/L) n` of
`IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity`.

## What is provided

* General odd `n`:
  `hasIntegralCoordinates_of_odd_torsion`, `pointField_finiteDimensional_of_odd_torsion`,
  `divisionField_finiteDimensional_of_odd_torsion`,
  `isGalois_finiteDimensional_normalClosure_of_odd_torsion`,
  `isOpen_fixingSubgroup_divisionField_of_odd_torsion`.
* Prime scenario (`ℓ` a prime of `ℤ`, odd, `(ℓ : K) ≠ 0`): the same five statements
  with `ℓ` in place of `n`.

## Scope and status of the hypotheses

Every statement below takes the bridge hypothesis `DivisionPolynomialDetectsTorsion`
as an input; this file does not prove the bridge for any new `n`, and the bridge
hypothesis is not eliminated.  What is new is that the hypotheses of the consumer's
finiteness, Galois-closure and Krull-topology statements are discharged from torsion
data instead of being assumed as integrality of coordinates.  The unconditional bridge
for general odd `n` remains open (three blocked routes are recorded in the header of
`EllipticTorsionAlgebraicity`).

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, torsion point, division field, integrality
-/

open WeierstrassCurve

namespace IUT.ABCBridge.Galois.EllipticTorsionConsumerWiring

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

section

variable [DecidableEq L]

/-! ## Assembly for general odd `n` -/

/-- **Coordinates of odd-torsion points are integral** over `K`.  From the bridge
interface for odd `n` with `(n : K) ≠ 0`, the coordinates of an `n`-torsion point of
the base change `E/L` satisfy the consumer's integrality hypothesis. -/
theorem hasIntegralCoordinates_of_odd_torsion (E : WeierstrassCurve.Affine K)
    (Q : (WeierstrassCurve.Affine.baseChange E L).Point) {n : ℤ}
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) n)
    (hodd : ¬ Even n) (hne : (n : K) ≠ 0) (hQ : n • Q = 0) :
    EllipticDivisionField.HasIntegralCoordinates K L E Q :=
  EllipticTorsionAlgebraicity.hasIntegralCoordinates_of_torsion K L E Q hbridge hodd hne hQ

/-- The coordinate field `K(Q)` of an odd-torsion point is finite-dimensional over `K`,
from the bridge interface. -/
theorem pointField_finiteDimensional_of_odd_torsion (E : WeierstrassCurve.Affine K)
    (Q : (WeierstrassCurve.Affine.baseChange E L).Point) {n : ℤ}
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) n)
    (hodd : ¬ Even n) (hne : (n : K) ≠ 0) (hQ : n • Q = 0) :
    FiniteDimensional K ↥(EllipticDivisionField.pointField K L E Q) :=
  EllipticTorsionAlgebraicity.pointField_finiteDimensional_of_torsion
    K L E Q hbridge hodd hne hQ

/-- The division field `K(P i : i)` of a finite family of odd-torsion points is
finite-dimensional over `K`, from the bridge interface. -/
theorem divisionField_finiteDimensional_of_odd_torsion (E : WeierstrassCurve.Affine K)
    {ι : Type*} [Finite ι] (P : ι → (WeierstrassCurve.Affine.baseChange E L).Point) {n : ℤ}
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) n)
    (hodd : ¬ Even n) (hne : (n : K) ≠ 0) (hP : ∀ i, n • P i = 0) :
    FiniteDimensional K ↥(EllipticDivisionField.divisionField K L E P) :=
  EllipticTorsionAlgebraicity.divisionField_finiteDimensional_of_torsion
    K L E P hbridge hodd hne hP

/-- **Finite Galois closure of the division field** from torsion data: if `L/K` is
Galois and the family is finite, the normal closure of `K(P i : i)` in `L` is a
finite-dimensional Galois extension of `K` containing it. -/
theorem isGalois_finiteDimensional_normalClosure_of_odd_torsion
    (E : WeierstrassCurve.Affine K) {ι : Type*} [Finite ι] [IsGalois K L]
    (P : ι → (WeierstrassCurve.Affine.baseChange E L).Point) {n : ℤ}
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) n)
    (hodd : ¬ Even n) (hne : (n : K) ≠ 0) (hP : ∀ i, n • P i = 0) :
    IsGalois K ↥(IntermediateField.normalClosure K
        ↥(EllipticDivisionField.divisionField K L E P) L) ∧
      FiniteDimensional K ↥(IntermediateField.normalClosure K
        ↥(EllipticDivisionField.divisionField K L E P) L) :=
  EllipticDivisionField.isGalois_finiteDimensional_normalClosure_of_hasIntegralCoordinates
    K L E P fun i => hasIntegralCoordinates_of_odd_torsion K L E (P i) hbridge hodd hne (hP i)

/-- The fixing subgroup of the division field is open in the Krull topology, from
torsion data. -/
theorem isOpen_fixingSubgroup_divisionField_of_odd_torsion (E : WeierstrassCurve.Affine K)
    {ι : Type*} [Finite ι] [IsGalois K L]
    (P : ι → (WeierstrassCurve.Affine.baseChange E L).Point) {n : ℤ}
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) n)
    (hodd : ¬ Even n) (hne : (n : K) ≠ 0) (hP : ∀ i, n • P i = 0) :
    IsOpen (EllipticDivisionField.divisionField K L E P).fixingSubgroup.carrier :=
  (EllipticDivisionField.isOpen_fixingSubgroup_divisionField_iff K L E P).mpr
    (divisionField_finiteDimensional_of_odd_torsion K L E P hbridge hodd hne hP)

/-! ## The prime scenario -/

set_option linter.unusedVariables false

/-- **Prime-`ℓ` scenario.**  For a prime `ℓ` of `ℤ` that is odd with `(ℓ : K) ≠ 0`,
the bridge interface for `ℓ` gives the integrality of the coordinates of `ℓ`-torsion
points. -/
theorem hasIntegralCoordinates_of_prime_torsion (E : WeierstrassCurve.Affine K)
    (Q : (WeierstrassCurve.Affine.baseChange E L).Point) {ℓ : ℤ}
    (hℓprime : Prime ℓ)
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) ℓ)
    (hℓodd : ¬ Even ℓ) (hℓne : (ℓ : K) ≠ 0) (hQ : ℓ • Q = 0) :
    EllipticDivisionField.HasIntegralCoordinates K L E Q :=
  hasIntegralCoordinates_of_odd_torsion K L E Q hbridge hℓodd hℓne hQ

/-- The coordinate field of a prime-torsion point is finite-dimensional over `K`. -/
theorem pointField_finiteDimensional_of_prime_torsion (E : WeierstrassCurve.Affine K)
    (Q : (WeierstrassCurve.Affine.baseChange E L).Point) {ℓ : ℤ}
    (hℓprime : Prime ℓ)
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) ℓ)
    (hℓodd : ¬ Even ℓ) (hℓne : (ℓ : K) ≠ 0) (hQ : ℓ • Q = 0) :
    FiniteDimensional K ↥(EllipticDivisionField.pointField K L E Q) :=
  pointField_finiteDimensional_of_odd_torsion K L E Q hbridge hℓodd hℓne hQ

/-- The division field of a finite family of prime-torsion points is
finite-dimensional over `K`. -/
theorem divisionField_finiteDimensional_of_prime_torsion (E : WeierstrassCurve.Affine K)
    {ι : Type*} [Finite ι] (P : ι → (WeierstrassCurve.Affine.baseChange E L).Point) {ℓ : ℤ}
    (hℓprime : Prime ℓ)
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) ℓ)
    (hℓodd : ¬ Even ℓ) (hℓne : (ℓ : K) ≠ 0) (hP : ∀ i, ℓ • P i = 0) :
    FiniteDimensional K ↥(EllipticDivisionField.divisionField K L E P) :=
  divisionField_finiteDimensional_of_odd_torsion K L E P hbridge hℓodd hℓne hP

/-- Finite Galois closure of the division field of prime-torsion points. -/
theorem isGalois_finiteDimensional_normalClosure_of_prime_torsion
    (E : WeierstrassCurve.Affine K) {ι : Type*} [Finite ι] [IsGalois K L]
    (P : ι → (WeierstrassCurve.Affine.baseChange E L).Point) {ℓ : ℤ}
    (hℓprime : Prime ℓ)
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) ℓ)
    (hℓodd : ¬ Even ℓ) (hℓne : (ℓ : K) ≠ 0) (hP : ∀ i, ℓ • P i = 0) :
    IsGalois K ↥(IntermediateField.normalClosure K
        ↥(EllipticDivisionField.divisionField K L E P) L) ∧
      FiniteDimensional K ↥(IntermediateField.normalClosure K
        ↥(EllipticDivisionField.divisionField K L E P) L) :=
  isGalois_finiteDimensional_normalClosure_of_odd_torsion K L E P hbridge hℓodd hℓne hP

/-- The fixing subgroup of the division field of prime-torsion points is open in the
Krull topology. -/
theorem isOpen_fixingSubgroup_divisionField_of_prime_torsion (E : WeierstrassCurve.Affine K)
    {ι : Type*} [Finite ι] [IsGalois K L]
    (P : ι → (WeierstrassCurve.Affine.baseChange E L).Point) {ℓ : ℤ}
    (hℓprime : Prime ℓ)
    (hbridge : DivisionPolynomialDetectsTorsion (WeierstrassCurve.Affine.baseChange E L) ℓ)
    (hℓodd : ¬ Even ℓ) (hℓne : (ℓ : K) ≠ 0) (hP : ∀ i, ℓ • P i = 0) :
    IsOpen (EllipticDivisionField.divisionField K L E P).fixingSubgroup.carrier :=
  isOpen_fixingSubgroup_divisionField_of_odd_torsion K L E P hbridge hℓodd hℓne hP

end

end IUT.ABCBridge.Galois.EllipticTorsionConsumerWiring
