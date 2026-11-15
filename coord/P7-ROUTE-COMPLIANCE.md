# P7 Route Compliance Correction

Date: 2026-11-15 20:20
User correction: do not follow own wrong ideas when the route file already gives construction methods.

## Deviations identified
1. Treated cards/S3135 conditional endpoints as mainline; route §1/§3 says mainline is actual N0-N11 and not hbound/hCor312/Nonempty.
2. N1 detour: pursued analyticity of inverse-j tateJQSeries at q=5; route §5.1 prescribes constructing actual q by fixed-point iteration q_{n+1}=t-q_n^2 g(q_n) on contracting disk, with |q|=|t|.
3. N5 detour: started from C3/base identities; route §9.1 prescribes actual finite product X_q/C_q/J_q and direct Haar volume identity V=-sum n_b f_b log p_b.
4. N3 detour: ambient embedding lemma; route §7.1-§7.4 prescribes nrm_norm/v_norm, completion transport, actual tensor decomposition, Gaussian log range.
5. Premature interface files (doc-only) were treated as progress; route requires actual producers.

## Correct execution order
- P1 §5.1 actual q fixed point; §5.2 coordinate conditions; §5.3 root embedding.
- P4 §9.1 product q tuple/divisor/volume; §9.2 repeated-factor weights.
- P5 §15.2 actual packet four-column table + Gamma_t subset H_t.
- P3 D1 fixed_degreeZero_units_equiv.
- P7 S1 l/isogeny height.
- P8 G1 Fermat cover/compactness.

## Rule
Route file is the sole construction spec. Any new bridge must first name its P-package and the route section; no ad hoc replacement.
