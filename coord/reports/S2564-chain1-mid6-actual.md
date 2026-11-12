# S2564 chain 1, sixth block: coefficients in degrees 401..480

Date: 2026-11-05
Owner: worker (subagent, parent session-f6ded1d8-b5c8-45b3-93ce-a5ae39a93db1)
Stage: proof (kernel closed), actual file
Consumer: the S2564 chain-1 assembly. With S2564Chain1LowActual (degrees 0..11),
S2561Mod613Chain1Actual.chunk0 (n <= 80) and the other Mid/High blocks, this
covers the remaining window [401,480] of the coefficient identity for
G * S0 = X^613 - T1 in (ZMod 613)[X].

## Target (locked)

For every n with 401 <= n <= 480:

    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n

The objects are LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.S0
(sum of the eight shifted blocks X^shift * R_i),
LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual.G and .T1.

## File

tmp/sheaf/xif/paper/S2564Chain1Mid6Actual.lean (1303 lines). Imports only
tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual,
tmp.sheaf.xif.paper.S2554Mod613ChainDataActual,
tmp.sheaf.xif.paper.S2562GmulCoeffActual,
tmp.sheaf.xif.paper.S2563R4LookupActual,
tmp.sheaf.xif.paper.S2563R5LookupActual.
No sorry, no native_decide, no new axiom, no extra hypothesis.

Auxiliary evidence file: tmp/sheaf/xif/paper/S2564Mid6Axiom.lean
(#print axioms on the block lemmas and on 7 sampled per-degree lemmas, plus an
example restating the exact task target through chain1_mid6).

## Proof (what is actually proved)

1. Degree bounds: R0.natDegree <= 80, R1..R4.natDegree <= 79, T1.natDegree <= 11
   (compute_degree!), hence R_i.coeff m = 0 beyond those degrees
   (coeff_eq_zero_of_natDegree_lt).
2. lhs_coeff_eq_zero: for 12 <= n < 613 the left hand side is
   (X^613).coeff n - T1.coeff n = 0 - 0 = 0 (coeff_X_pow and the T1 bound).
3. S0 windows (S0 unfolds as the sum of its eight shifted blocks, each through
   its S0_i_coeff if-lemma):
   * S0_coeff_389_400: for 389 <= k <= 400 only S0_4 = X^321 * R4 is active,
     so S0.coeff k = R4.coeff (k - 321). The pieces S0_0..S0_3 have degree at
     most 320, and S0_5, S0_6, S0_7 start at 401, 481, 561.
   * S0_coeff_401_480: for 401 <= k <= 480 only S0_5 = X^401 * R5 is active,
     so S0.coeff k = R5.coeff (k - 401). Here S0_4 has degree at most 400.
4. S0 coefficient lookup: the 92 lemmas S0_coeff_389 .. S0_coeff_480 give the
   explicit value in ZMod 613, restricted from the corresponding S2563R4 /
   S2563R5 lookup lemma (R4_coeff_68 .. R4_coeff_79, R5_coeff_0 .. R5_coeff_79).
5. 13 coefficients of G are pre-proved once (G_coeff_0 .. G_coeff_12, by
   simp [G]) and used as rewrite rules, instead of re-unfolding G per degree.
6. chain1_coeff_n for each n in [401,480]: rewrite the right hand side with
   G_mul_coeff_ge S0 n (12 <= n) and the left hand side with lhs_coeff_eq_zero,
   expand the 13-term support sum (Finset.sum_range_succ), normalise the
   numeral arguments n - a, rewrite the 13 lookups S0_coeff_(n-12)..S0_coeff_n
   and the 13 G coefficients, and close the resulting identity in ZMod 613 by
   decide (kernel computation, not native_decide).
7. chain1_mid6 (n) (401 <= n) (n <= 480): the 80 per-degree lemmas repackaged
   as one quantified statement by interval_cases followed by a first/exact
   dispatch.

## Verification actually run

* serial compile, exactly the prescribed policy command:
  cd D:/lean; lake env lean -j1 -R 'D:/lean' -o
  '.lake/build/lib/lean/tmp/sheaf/xif/paper/S2564Chain1Mid6Actual.olean'
  'tmp/sheaf/xif/paper/S2564Chain1Mid6Actual.lean'
  EXIT = 0, 182.93 s, no errors and no warnings (build log is empty).
* SRC SHA256 1F0473F46A40E2016C55C851B55380DFDAE5808F88704BE6F9E913F6247FAD26
  (72566 bytes).
* OLEAN SHA256 C4DBE8F2F8ABFA0CC1FD2830B192760F539C4F365BA98D849C5F41EE694E15C1
  (4263088 bytes), .lake/build/lib/lean/tmp/sheaf/xif/paper/.
* #print axioms run (S2564Mid6Axiom.lean, EXIT = 0, 88.2 s) on
  S0_coeff_389, S0_coeff_400, S0_coeff_401, S0_coeff_480, S0_coeff_389_400,
  S0_coeff_401_480, chain1_coeff_401, chain1_coeff_412, chain1_coeff_413,
  chain1_coeff_440, chain1_coeff_479, chain1_coeff_480, chain1_mid6:
  every one depends on [propext, Classical.choice, Quot.sound] only.
* target-type check: the same file contains
  example : forall n, 401 <= n -> n <= 480 ->
    ((X : (ZMod 613)[X])^613 - T1).coeff n = (G * S0).coeff n
  proved by chain1_mid6 (EXIT = 0).

## Statement / proof status

statement_compiles: yes (olean built)
proof_body_checked: yes (no sorryAx anywhere in the axiom prints)
kernel_closed: yes, axioms trio only
target_accepted: type-checked restatement of the locked target in the same
toolchain; not independently reviewed by a maintainer in this session.

## Boundary / notes

* Name ambiguity: the repository also defines root-level R0..R5 over ZMod 29
  (S2122/S2126 chain, reachable through S2553), so every reference to the
  mod-613 blocks in this file is written with the full name
  LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.Ri.
* The numeric relation is a genuine cancellation: for n >= 413 all thirteen
  terms come from R5, and G*R5 has zero coefficients in degrees 12..79; for
  401 <= n <= 412 the window mixes R4 (degrees 389..400) with R5. Both are
  certified by decide inside the kernel, not by an external computation.
* An independent Python computation over ZMod 613 reproduced
  ((X^613 - T1).coeff n = (G*S0).coeff n) for all 0 <= n <= 620, i.e. the
  identity of this block is not a local accident of the window.
