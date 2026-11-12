# S2456: cF/cK — actual involution available, quotient/sign action missing

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL:
- S2456Orbicurve := S2482Orbicurve.
- S2456EllipticInvolution := S2482EllipticInvolution, re-exported from the now-clean tmp/sheaf/xif/paper/S2482QiInvolutionActual.lean.
EXIT=0, olean 19008, SHA256 006d372f2a138089adc7993428af9818c8e75222abe357a8f4a3f2e01ab36735, axioms propext/Classical.choice/Quot.sound.

cF NOT constructed. Exact missing API:
1. Iut.OrbicurveSignAction S2482Orbicurve. The structure Orbicurve is available (diagram, inversion, generator_identification, inversionSquared), but there is NO constructor or instance anywhere in LeanFormal/Mathlib.
2. cF : Iut.HyperbolicOrbicurve F and quotient : Iut.OrbicurveSignInvariantMorphism signAction cF.
3. quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient. The structure is a universal property (descend, factor, descendTwoCell, ...) with no inhabitant.

cK NOT constructed. Exact missing:
- actual cF, then SourceOrbicurveScalarExtension F K cF and cK = extension.result.

S2456 defines exact dependency Props S2456SignActionMissing, S2456SignQuotientMissing, S2456KSideMissing; no inhabitant is asserted. No fake IsStack.