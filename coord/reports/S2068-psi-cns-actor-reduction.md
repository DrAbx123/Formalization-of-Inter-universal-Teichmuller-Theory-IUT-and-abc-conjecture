# S2068: Psi_cns and O^×mu actor conditional reductions

Date: 2026-11-02. Layer O. No all-units/IndIntegralMonoid/SourceMLF.

## Actual file

tmp/sheaf/xif/paper/S2068PsiCnsActorReduction.lean
Source SHA256 e8b52ba1908c2a12f5c692f29e05d1395bc9d9f78b15dbc99085830c95f69c87
olean SHA256 bcc66e5b0211f081334f6d027626e6dd7189755e72d094ca7d2e04d8d3024580
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## (b) Psi_cns conditional reduction

S2068PsiCns N := PsiCns p N is the actual cohomological submonoid of
PsiCnsCohomology p, and S2068PsiCnsOne gives its unit.
S2068PsiCns_equiv_otriFv:
  (N : PsiCnsNormalization p) -> NormalizationIsValuation p N ->
  PsiCnsExhaustion p N -> Nonempty (S2068PsiCns p N ≃* OtriFv p),
the actual identification with the local integral monoid.

Exact missing (M4/d):
S2068M4NormalizationRequired := NormalizationMissing p
(Nonempty (PsiCnsNormalization p)),
S2068Cor110bRequired := Cor110bKummerIdentification p
(normalization + valuation + exhaustion).
No normalization is asserted or constructed.

## (c) O^×mu actor conditional assembly

S2068GroupAlgorithm has alg : ProfiniteGrp -> Type, commMonoid instances, and
algMap functoriality. S2068OUnitsMuActorAssembly adds the local
actor_equiv_local fields and action at PaperV. From it,
S2068OUnitsMuActorOfAssembly constructs S2038's OUnitsMuActor with no fake
field.

Exact missing: an inhabitant of S2068GroupAlgorithm /
S2068OUnitsMuActorAssembly, i.e. the IUT II Example 1.8(iii)-(iv) group
algorithm. No algorithm is asserted.

## Consumers

S2038 PaperOActual fields (b) and (c). No all-units carrier, no
IndIntegralMonoid, no SourceMLF, no qVFamily.
