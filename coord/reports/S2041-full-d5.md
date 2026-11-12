# S2041: full D5 l=5 large-image — status after S2056/S2057

Date: 2026-11-02. No native_decide, no axiom, no sorry, no fake.

## Closed upstream

- S2055: Dickson classification and all three S2014 components.
- S2056Psi5RootsActual: actual Galois-equivariant bijection between the twelve
  roots of prePsi_5 and the twelve pairs {+-P}; root card 12, torsion card 25,
  fibre card 2, all kernel checked.
- S1999/S2005/S2003: splitting-field, F'-group and quadratic-subfield bridge.

## New actual S2057 results

tmp/sheaf/xif/paper/S2057DedekindFrobBridgeActual.lean:

- s2057InertiaDeg_eq_natDegree: actual Kummer--Dedekind reduction.  For any
  number field K, integral theta, prime p not dividing the conductor exponent,
  and Q in monicFactorsMod theta p whose corresponding prime is P,
  P.inertiaDeg Z = Q.natDegree.  This is the "factor degree = residual degree"
  step, now an actual Mathlib instance rather than a missing statement.
- S2057Psi5Q := S1667Curve.prePsi 5, S2057Psi5F its base change to F'.
- S2057Psi5Q_separable, S2057Psi5F_separable (S1942 certificate + map).
- S2057FiveDivisionField := SplittingField S2057Psi5F.
- S2057FiveDivisionField_isGalois: actual IsGalois F' S2057FiveDivisionField
  from separability of the splitting field.

## Exact remaining structures (no inhabitant)

- S2057Mod29FactorizationData: integer model of psi5, reduction modulo 29,
  irreducible factors of degrees 2 and 10, and their product equality.
- S2057FrobMod29CycleTypeBridge: a Frobenius element of Gal(F'/Q), a
  permutation of S2056Pair with cycle type (2,10), and the mod-29
  factorization data.
- S2057RangeHypothesesData b: the three actual range hypotheses
  (DetSurjectiveOn, PairTransitive, HasCycleType102) at a fixed basis.

## Final assembly

s2057Target_of_rangeHypotheses: S2057RangeHypothesesData b ->
S1987D5LargeImageFive, via S2055LargeImage_of_dickson and
S1987D5LargeImageFive_of_fullRange.

Thus the remaining work is exactly the two exact S2057 structures (mod-29
factorization and Frobenius cycle type), plus the Weil-pairing/determinant
identification that supplies the determinant range hypothesis.

## Artifact hashes

S2041D5LargeImageFirstMilestoneActual.lean:
- 134 lines, 5968 bytes
- SHA256 f4f2bb846687312b24c828957e330905199f2cec5d93ad6c275949d202f95787
- EXIT=0
- olean 37264 bytes, SHA256
  e0f3052a3a3182cd7e62a6526e7c6c2ed275bbab3e99b716641b9d15e4db5164

S2057DedekindFrobBridgeActual.lean:
- 122 lines, 5171 bytes
- SHA256 bffe0c9275a483e2cc55831e986898971e32d37b315d4710353b5da6c5448c84
- EXIT=0
- olean 150680 bytes, SHA256
  303cc05dbda82f3dcd70ecb12debf5a4afadbc7c23c006823f021a6e012e8864

S2056Psi5RootsActual.lean (upstream):
- 556 lines, 23606 bytes
- SHA256 1d6031ca62dd6be6ab3fc4145ad942661a7b9b73287b13525791b6d5868ee739
- olean 408200 bytes, SHA256
  9b9ada9b4f0fa6bd3cd1c8e61f20045b60ac419bfd67e59465d257c6193e0d1c

Axiom footprint of s2057InertiaDeg_eq_natDegree, S2057Psi5Q_separable,
S2057Psi5F_separable, S2057FiveDivisionField_isGalois and
s2057Target_of_rangeHypotheses: [propext, Classical.choice, Quot.sound].
