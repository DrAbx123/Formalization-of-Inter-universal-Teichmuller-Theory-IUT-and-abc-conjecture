# J1-M mass derivation (kurt, 2026-11-17 03:10Z) — one page for david/Lead audit

Status: derivation draft for audit; no Lean changed.

## 1. Route formula (verbatim, route section 5.3 J1 L412-418)

  (1/[L:Q_p]) * log(mu_L(rO_L)/mu_L(O_L)) = log|r|_p = (1/(2l)) log|q|_p,
with |.|_p the extension of |p|_p = p^{-1}, and q = r^{2l} (Kummer root extension L/K_w).
If the source q-marker stores q_b rather than r_b, first prove the Kummer-root region is
{x : |x|_p^{2l} <= |q_b|_p} = r_b O_L; the SAME root-region interpretation must be used on the theta
side. Weighting with the P4 divisor/weight dictionary yields -M.

## 2. Normalizations (to fix and keep identical on both sides)

- |.|_p on Q_p: |p|_p = p^{-1}; v_p(x) := -log_p |x|_p, so v_p(p) = 1.
- Fmod_b/Q_p with uniformizer pi_b, p = u*pi_b^{e_b}: |pi_b|_p = p^{-1/e_b}, so v_p(x) = v_b(x)/e_b
  where v_b is the pi_b-adic valuation with v_b(pi_b)=1.
- Kummer: |q|_p = |r|_p^{2l} gives v_p(q) = 2l*v_p(r), hence
  log|r|_p = (1/(2l)) log|q|_p (route formula (1) above).
- Per-b M form (Lead's): M_b = (lambda_b/d_mod)*(v_p(q_b)/(2l))*log p_b, where
  lambda_b = [Fmod_b:Q_p] = e_b f_b and d_mod = [Fmod:Q].
  We must fix v_p(q_b) := ord_b(q)/(e_b f_b) to make this equal to MpaperB_b:
  (e_b f_b/[Fmod:Q]) * (ord_b/(2l e_b f_b)) logp = ord_b/(2l[Fmod:Q]) logp, matching
  M_paper_v2 = (1/(2l))(1/[Fmod:Q]) Sum_b ord_b(q) logp_b from david's fiber_sum_ef.
  EQUIVALENTLY: with the uniformizer normalization v_p = v_b/e_b of item 2, ord_b above is the
  DEGREE-NORMALIZED order ord_b = e_b f_b v_p(q_b). The audit point is: whichever convention is
  used, lambda_b* v_p(q_b) must collapse to ord_b/(2l d_mod).

## 3. Theta side (the correction)

- Current KSide: c_root = actualRootCoeff = c_norm/(2l) with c_norm = ord_P(q) (P = selected
  F-place lift), and arithmeticTupleNormalizedLogVolume divides by [K_w:Q_p] = e_w f_w.
  So theta_b^{(current)} = -(ord_P/(2l)) logp / e_w, which is NOT the route theta scale.
- Route says the theta end must use the SAME root-region interpretation with coefficient
  v_p(q_b)/(2l) (not ord_P/(2l)); the corrected reading is
  thetaM_b = -(v_p(q_b)/(2l)) log p_b  = -M_b,
  provided the normalized log volume is taken with respect to [L:Q_p] (Kummer extension), or the
  [K_w:Q_p]-division is compensated by an explicit index/different correction assigned to C1
  (route allows: Haar rescaling cancels in differences; different reference lattices leave
  index/different corrections in C1).
- Consequence: thetaP5M := Sum_b lambda-weighted thetaM_b with the P4 dictionary = -M_paper_v2
  exactly (no inequality needed), and C2 lower becomes -M <= thetaP5M <= H_pkt with thetaP5M the
  new M-scale object (NOT the current ksThetaHullLogRoot_lam).

## 4. Region directions (open audit point)

Let F(c) be the tensor-lattice region with coefficient c. Larger c = smaller region. The current
theta source span uses urCeilC = ceil(c_root) >= c_root, so F(c_root) is LARGER than F(urCeilC):
q-root region contains the label-1 theta region, not the reverse. For the lower bound -M <= theta
we need qRoot >= ... wait: mass monotonicity requires qRoot SUBSET theta hull. With c_root <= urCeilC
we get F(c_root) SUPERSET F(urCeilC) = thetaSourceSpan, so qRoot subset theta hull is FALSE unless
the theta coefficient is chosen as ceil of the ROOT coefficient itself (i.e. F(urCeilC) = F(c_root)
when c_root is integral / the root generator is exactly the pure generator with coefficient
c_root). ROUTE RESOLUTION: use the root-region interpretation on BOTH sides with the same
coefficient v_p(q_b)/(2l), so the two regions coincide; then containment is an equality of regions
and the mass comparison is exact. This is why the theta coefficient MUST be corrected (item 3),
not merely rescaled by a constant.

## 5. Concrete plan (after audit approval)

1. New file Mzk1URThetaKLambdaMScaledActual (already drafted, abstract): ThetaMScaleData with
   eFiber/etc.; add coefficient v_p(q_b)/(2l) reading.
2. Kummer mass: (1/[L:Q_p]) log(mu(rO)/mu(O)) = log|r|_p via DVR index (cardQuot_pow_of_prime /
   absNorm_* / absNorm_prime_eq_pow_inertiaDeg) + Haar subgroup index (index_mul_measure).
3. qRoot region = r_b O_L with |r_b|_p^{2l} = |q_b|_p, and SAME coefficient reading on the theta
   hull (corrected definition).
4. Weighted sum with lambda_b/d_mod -> -M_paper_v2 (fiber_sum_ef telescope).
5. thetaSourceHull subset packetHull (closure + possibleImages subset) => thetaP5M <= H_pkt.
6. Compose -M_paper_v2 <= thetaP5M <= H_pkt (non-strict, route L404/L423).

## 6. Audit questions for david/Lead

Q1. Confirm v_p(q_b) := ord_b/(e_b f_b) (with ord_b the paper degree-normalized order) and the
    lambda_b = e_b f_b convention, so that M_b = ord_b/(2l d_mod) logp.
Q2. Confirm the theta normalized log volume should be taken w.r.t. [L:Q_p] (Kummer) as in route,
    and which index/different correction goes to C1 if [K_w:Q_p] is used.
Q3. Confirm the root-region equality on both sides (item 4), i.e. the theta coefficient
    v_p(q_b)/(2l) makes qRoot region and theta source region coincide.

## 7. Audit resolutions (Lead ruling 2026-11-17 03:30Z): Q1/Q2/Q3 APPROVED

Q1 (approved): v_p(q_b) := ord_b/(e_b f_b) (paper degree normalization), so
   M_b = (lambda_b/d_mod)*(v_p(q_b)/(2l))*log p = ord_b/(2l[Fmod:Q])*log p,
   matching M_paper_v2. Equivalent form using localNormOrder and
   ord_P = e_{P|b} ord_b, [F_P:Qp] = e_{P|b} f_{P|b} e_b f_b.
Q2 (approved): the theta side uses the SAME coefficient v_p(q_b)/(2l) (same root-region
   interpretation), giving thetaM_b = -(lambda_b/d_mod)*(v_p/(2l))*log p = -M_b termwise.
   The old reading with c_root = ord_P/(2l) is marked LEGACY; the e_w f_w normalization
   difference is assigned to C1 as an index/different correction (documented, not silently dropped).
Q3 (approved): with the same coefficient on both sides the q-root region and the theta source
   region COINCIDE (equality), so containment no longer relies on c_root <= urCeilC. That
   inequality is used only for the OLD measure upper bound (ksThetaHull subset ceilRegion) and
   must not be used for (b).
Additional ruling: the upper bound uses CONTAINMENT (route L420): thetaSourceHull subset
packetHull => thetaP5M <= (packet hull log volume upper bound) <= H_pkt, via C1's V/average with
the same v_p normalization on V (write V_M per term if needed). No per-b ksCeilC monotonicity.

## 8. Lean plan for Mzk1URThetaSourceHullActual (after Q1-Q3)

1. thetaSourceSpan/thetaSourceHull defs (DONE, file queued).
2. (a) source generator in span via phi=id witness; (b) O-saturation O_hol • span subset span and
   lifted to the hull (closure).
3. Kummer mass: (1/[L:Q_p]) log(mu(rO)/mu(O)) = log|r|_p, with DVR index
   (Ideal.cardQuot_pow_of_prime, Ideal.absNorm_apply/span_singleton, project
   absNorm_prime_eq_pow_inertiaDeg*) and Haar subgroup index (Subgroup.index_mul_measure); q = r^{2l}.
4. same-coefficient region equality qRoot = thetaSourceSpan (Q3) => mass(theta) = -M_b per b.
5. lambda/d_mod weighted sum with fiber_sum_ef telescope => thetaP5M = -M_paper_v2 (termwise).
6. thetaSourceHull subset packetHull (closure_minimal + possibleImages subset + local closedness
   proof if the actual-packet file is red) => thetaP5M <= H_pkt.
7. Compose -M_paper_v2 <= thetaP5M <= H_pkt (non-strict, route L404/L423).
