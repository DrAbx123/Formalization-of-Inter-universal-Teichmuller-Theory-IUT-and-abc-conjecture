# N8 stage3 proof-writing batch (2026-10-23)

User instruction: write a lot first, compile centrally later.

| task | owner | draft | target |
|---|---|---|---|
| S3-1 | qside | ThetaValueCompletion.lean + STAGE3.md | actual Real theta -> completion map for T11 |
| S3-2 | logdescent | SourceQRealReadout.lean | actual source q-pilot Real readout for C9 |
| S3-3 | multiradial | C4IQAlignment.lean | C4 value-monoid vs T11 IQ alignment/no-go |
| S3-4 | transport | DegreeComparisonIQProof.lean | C8 iqDegree=iqMuLog proof |
| S3-5 | kummer | HolomorphicHullExistence.lean | C7 actual hull inhabitant |
| S3-6 | volumedet | C6NormalizationProof.lean | C6 normalized vs IQ mu_log bridge |
| S3-7 | primespine | C013Existence.lean | C0/C1/C3 existence |
| S3-8 | iplsheapt | AlgorithmCompatibilityProof.lean | C5 actual compatibility instance |

Acceptance for this batch: proof sketches/Lean drafts, exact gaps; no central compile yet.
Then lead does a batch compile and updates DAG/sorry registry.