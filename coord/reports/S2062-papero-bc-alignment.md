# S2062: S2038 (b)/(c) alignment after S2060

Date: 2026-11-02. Layer O. Canonical completion carrier: S2060/S2055 integral
units. No S2035 all-units carrier is used for PaperO.

## Verified S2060 actual completion data

File: tmp/sheaf/xif/paper/S2060CompletionUnitsActual.lean
Source SHA256 b26e41ed712377ba4d6beb8cd0a8912fef4a0a573f2a234ec95ab7a9e27253fe
olean SHA256 51c41b149782a0d144bc1b4cf88113d61b8bd31cb3d461b8aab6a155bda00f6b
EXIT=0. Axioms [propext, Classical.choice, Quot.sound] for:
s2060AlgClosureEquiv, s2060AlgClosureEquiv_norm,
s2060CompletionIntegralUnitsEquiv,
s2060CompletionIntegralUnitsEquiv_normCompatible,
s2060PaperOUnitsMuAmbient.

S2060 constructs the actual norm-preserving Q_p-algebra equivalence
s2060AlgClosureEquiv :
  SourceAlgebraicClosure (qVPlace T b) ≃ₐ[PadicScalarField]
  AlgebraicClosure (PadicScalarField),
proves norm preservation, induces
s2060CompletionIntegralUnitsEquiv :
  (Integers (SourceAlgebraicClosure (qVPlace T b)))^x ≃*
  LocalOFieldUnits (s2060Prime T b),
proves norm compatibility, and constructs s2060PaperOUnitsMuAmbient.

This closes the completion-carrier/norm gap that S2056/S2057 reduced to
S2056ClosureIsometry for the rational-place case. The S2060 construction is the
general number-field-place version and is the one to use.

## S2038 alignment

S2038 PaperOActual fields:

(a) CurvePiOneData: exact missing actual punctured-curve etale/tempered pi_1
    with nontrivial geometric kernel.
(b) ThetaMonoidActual: exact missing. S1973 supplies only the local-field
    PsiEnv/PsiGau model; the cohomological Psi_cns of IUT II Cor 4.6(iv) and its
    identification with the actual local integral monoid are not constructed.
(c) OUnitsMuActor: the local carrier and O^mu identification are now actual via
    S2060/S2055. The remaining exact missing is the group-theoretic algorithm
    alg : ProfiniteGrp -> Type of IUT II Example 1.8(iii)--(iv), its
    functoriality algMap, and the action field. These are fields of the S2038
    structure, not supplied by the local carrier.
(e) OperationKummerEvaluation: consumes (b) and (c); still missing.
(d) q-pilot is S2038's constructed field; not touched here.

No new carrier, no duplicate of (d), no all-units carrier for PaperO.

## First actionable

Construct alg : ProfiniteGrp -> Type from the Example 1.8(iii)--(iv) algorithm,
then its functoriality and action; this is the remaining part of (c). (b)
requires the cohomological Psi_cns assignment.
