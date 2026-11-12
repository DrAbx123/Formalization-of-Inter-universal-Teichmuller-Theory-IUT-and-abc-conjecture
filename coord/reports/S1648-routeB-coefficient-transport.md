# S1648 Route B: coefficient transport and rational/Qp comparison

Date: 2026-10-31. Report only; no new Lean.

Layer: B (with F consumer)
Source object: fixed source tuple (I, n, vQ, j, t), actual finite factors
  M_i = CommonPrimeCompletion (t i), rational ActualTensorSpan
  RatT = tensor over Q of M_i, Qp block SourceBlk = tensor over Qp of M_i.
Domain: RatT tensor[Q] Qp, and RatT itself; coefficient readouts qVFamily /
  qVFamPureCoefficient / qVFamNormalizedCoefficient.
Direction: actual construction / canonical surjection, not equivalence;
  coefficient transport c_pure and c_norm remain distinct.

BUILT:
- S1514 actual canonical Qp-linear map
    canonicalMap : (RatT tensor[Q] Qp) -> QpTensor,
  with canonicalMap_tmul, canonicalMap_tprod, canonicalMap_surjective,
  canonicalMapQuotientEquiv and canonicalMap_ker_iff;
- source-level sourceCanonicalQpMap with sourceCanonicalQpMap_tprod and
  sourceCanonicalQpMap_surjective for the fixed tuple;
- S1474 rational ActualTensorSpan / ProductDistribution / FieldDecomposition /
  LogShellRealization / Transport.

PROVED:
- the canonical rational->Qp comparison is surjective, not injective;
- kernel/quotient description via canonicalMapQuotientEquiv/canonicalMap_ker_iff;
- full index Capsule j and every factor CommonPrimeCompletion (t i) retained.

MISSING:
- coefficient transport comparison between RatT and QpTensor: the map is not
  an equivalence (infinite-dimensional Qp kernel), so no equivalence statement;
- c_pure = r_F * f and c_norm = r_F / e are distinct; c_pure = c_norm is
  equivalent to e*f = 1 and is not unconditional;
- no actual integral-lattice comparison RatT_lattice -> QpTensor with
  Z_p/finite-rank structure; S1474 rational level is IQSpan = top, not a
  finite lattice;
- no source-identification of qVFamily coefficient with the canonical map's
  scalar factor.

Consumer: F (Route F xi-f source bridge), via the fixed tuple comparison;
  not E1/E2, not O-layer PaperQPilotObject.

Reports read:
- coord/MAINLINE_ABC_F.md
- coord/reports/gap-exploration-20261030.md (alternate routes)
- coord/reports/S1449-report-ABC-graph.md section 0
- D:/lean/心得.md
- coord/ACTUAL-OBLIGATIONS-CLASSIFICATION.md

Conclusion:
- BUILT: S1514 canonical Qp-linear surjection + kernel/quotient for the fixed
  source tuple; S1474 rational tensor donors.
- PROVED: surjectivity and non-equivalence; factors/index retained.
- MISSING: exact coefficient transport c_pure/c_norm and integral-lattice
  comparison.  Do not claim equivalence or interchange c_pure with c_norm.
- No new Lean file; report EXIT=0.
