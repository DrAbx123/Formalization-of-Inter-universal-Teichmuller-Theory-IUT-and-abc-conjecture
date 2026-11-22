# R2 hsQ support doc: s^Q = actual distinguished-support primorial (dictionary owner: sophie)

Status: paper-dictionary ruling for R2 (canonical; cite in R2 code/docstrings). Lean names current.

## 1. Paper definition of the distinguished support (IV L1436-1460)

- IV L1438-1439: `V(F□)^dst ⊆ V(F□)^non` is the set of "distinguished" nonarchimedean
  valuations v "that extend to a valuation ∈ V(K)^non that ramifies over Q".
- IV L1443-1445 (D0): if v ∈ V(Ftpd)^non does not divide 2·3·5·l and is not contained in
  Supp(q_Ftpd^ADiv), then K/Ftpd is unramified over v.
- IV L1456-1460: for v ∈ V(F□)^non the following are equivalent:
  (D1) v ∈ V(F□)^dst;
  (D2) v either divides 2·3·5·l or lies in Supp(q_F□^ADiv + d_F□^ADiv);
  (D3) the image of v in V(Ftpd) lies in V(Ftpd)^dst.
- IV L1452-1455: K contains a primitive 4·3·5·l-th root of unity, hence is ramified over Q
  at any v dividing 2·3·5·l (so those primes are always in the distinguished support).

## 2. The support divisor and log (IV L1467-1501)

- IV L1467-1475: `s^F*^ADiv := Σ_{v ∈ V(F*)^dst} e_v · v` (F* ∈ {Fmod, Q}).
- IV L1478-1481: `log(s^F*_vQ) := deg_{V(F*)_vQ}(s^F*^ADiv)`.
- IV L1482-1484: `log(s^F*) := deg(s^F*^ADiv)`.
- For F* = Q: e_v = 1 (Q has no ramification), hence
  `log(s^Q) = Σ_{wQ ∈ V(Q)^dst} log p_wQ` — the log of the primorial of the DISTINCT
  rational primes in the actual distinguished support. This is exactly our
  `Mzk1ULSQPaperFinalActual.log_sQPaper_eq_sum_log_paper` (DONE 10:29:11, unconditional).
- IV L1485-1492: `s^≤^ADiv := Σ_{wQ∈V(Q)^dst} ι_wQ log(p_wQ)·wQ` (ι_wQ a cutoff indicator)
  is a DIFFERENT object: it carries coefficient log p_wQ (times ι) on the Q-divisor, not
  the primorial count; `log(s^≤)` is therefore not `log(s^Q)`.

## 3. Our Lean implementation (current, three-axiom)

- `Mzk1ULSQPaperActual.sQPaper := ∏_{p ∈ qSupportPrimes ∪ dSupportPrimes ∪ specialPrimes l} p`
  with `qSupportPrimes = image(badFPrimeSet)`, `dSupportPrimes = image(differentPlaces)`,
  `specialPrimes l = {2,3,5,l.value}`.
- `Mzk1ULSQPaperFinalActual.log_sQPaper_eq_sum_log_paper :
  Real.log (sQPaper T) = ∑ p ∈ (qSupportPrimes ∪ dSupportPrimes ∪ specialPrimes l), log p`
  (unconditional; support positivity via `Mzk1ULSQPositivity2/3Actual`).
- `Mzk1ULSQPositivity3Actual.{qSupportPrimes_ne_zero, dSupportPrimes_ne_zero}`.
- `Mzk1ULSpecialPrimesOwnActual.specialPrimes_log_sum_le_own :
  ∑_{p ∈ specialPrimes l} log p ≤ 5 + log l` (replaces the retired sorryAx donor).

Alignment: `qSupportPrimes ∪ dSupportPrimes ∪ specialPrimes l` realizes (D2): primes
dividing 2·3·5·l (the `specialPrimes` part, l = the prime parameter) together with the
images of Supp(q^ADiv) (badFPrimeSet) and Supp(d^ADiv) (differentPlaces).

## 4. Rejected variants (do NOT use for R2)

- **urSQ(max bad prime) enlargement**: rejected. It includes primes not in (D2)'s support
  (i.e. primes ≤ max that divide neither 2·3·5·l nor q^ADiv+d^ADiv), violating IV L1467-1484;
  s^Q is the primorial of the ACTUAL distinguished support, not a max-bound primorial.
- **s^≤ (ι cutoff version)**: rejected as a replacement for s^Q. IV L1485-1492 defines it as
  a coefficient-log-p divisor (Σ ι_wQ log p_wQ · wQ), a different object; its log is not
  the primorial log used in IV L1563-1572.

## 5. Downstream constants (paper lines)

- IV L1555-1562: per-place `log(s^Fmod_vQ) ≤ 2·(log d^Ftpd_vQ + log f^Ftpd_vQ)` (Prop 1.3(i)).
- IV L1563-1571: dividing by p_vQ gives the (2/p_vQ)(...) per-place bound.
- IV L1572: `log(s^Q) ≤ 2·d_mod·(log d_Ftpd + log f_Ftpd) + log(2·3·5·l) ≤ 2 d_mod(...) + 5 + log l`;
  d_mod = [Fmod:Q] (IV L1006-1008); the special-prime constant is ours
  `specialPrimes_log_sum_le_own` (5 + log l).

## 6. R0.3 / D consumer line refs (kept for david)

- `D(L) = log|disc L|/[L:Q] = log(rootDiscr L)` (Mathlib rootDiscr definition); our
  `Mzk1ULPaperLettersActual.logDifferentF` is exactly D(L).
- h slot: `hBar L x = (1/[L:Q]) · Height.logHeight₁ x` (Height.logHeight₁ is
  unnormalized; see `ABCHeightArithmeticWeightComparison.lean:7-26`).
- Paper lines: IV L1206-1235 (Def 1.9 normalized degree), L1309-1313 (conductor),
  L1411-1425 (S_ar F vs Ftpd ≤ 21), L2483-2488 (C2 display), L1359-1364 (|log q|=(1/2l)log q).
