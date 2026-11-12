# S2069: exact gap for the group algorithm of IUT II Example 1.8(iii)-(iv)

Date: 2026-11-02. Layer O. No fake/all-units/IndIntegralMonoid.

## File

tmp/sheaf/xif/paper/S2069GroupAlgorithmGap.lean
Source SHA256 7c892525e233e8a4d27e5573bf0c6fab8cd3d874bd441fa0d505bb8afdd02d68
olean SHA256 a9ca1d1147f6558f29eef99bfba2dbe92f155ea308361bb548586cf721058dbd
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## What is done

S2069GroupAlgorithmReconstruction is the exact missing group-theoretic datum:

  units : ProfiniteGrp -> Type
  commMonoidUnits : forall G, CommMonoid (units G)
  map : G ~= H -> units G ~= units H

S2069GroupAlgorithmOfReconstruction turns it into S2068GroupAlgorithm
(alg, commMonoidAlg, algMap). Thus once the Ex1.8(iii)-(iv) algorithm exists,
the S2068 actor assembly consumes it without further gap.

S2069GroupAlgorithmRequired is the exact first missing type.

## Why no candidate is constructed

A candidate alg built only from continuous finite quotients does not know a
local field, so it cannot be O-times-mu(G). The paper's Ex1.8(iii) uses

  O^x(G) = lim_{H open in G} (O_{L_H})^x

where L_H is the local field cut out by H; Ex1.8(iv) quotients by roots of
unity. The tree has KappaOrbitUnitsActionDatum and
SourceKappaOrbitUnitsActionSupply only after an FPrimeStrip/upper local-field
datum is given; it has no functor ProfiniteGrp -> local field (local anabelian
reconstruction), and no group-theoretic construction of O^x(G) from G alone.
Therefore the missing definition/lemma is exactly Ex1.8(iii) (the limit
O^x(G)) plus Ex1.8(iv) (the O^mu quotient), or equivalently the local field
reconstruction that supplies the L_H.

No arbitrary candidate is installed; no inhabitant of
S2069GroupAlgorithmRequired is asserted.
