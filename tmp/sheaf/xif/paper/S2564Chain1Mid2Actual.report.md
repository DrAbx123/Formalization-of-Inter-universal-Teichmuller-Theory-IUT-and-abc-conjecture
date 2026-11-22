# S2564Chain1Mid2Actual — report (2026-11-05)

Range: n in [81, 160].
Target: `((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n`.

Deliverable: `tmp/sheaf/xif/paper/S2564Chain1Mid2Actual.lean` (1355 lines, 65911 bytes).
Contents:
* 92 S0 lookups `S0_coeff_69` .. `S0_coeff_160` (S0 expanded into its 8 shifted
  pieces, `S0_i_coeff` if-conditions; blocks 2..7 are inactive on this range since
  they start at 161, 241, 321, 401, 481, 561; block 0 is read off `R0_coeff_*` on
  69..80 and killed by `deg R0 <= 80` beyond, block 1 is read off `R1_coeff_*`);
* 80 target lemmas `chain1_coeff_81` .. `chain1_coeff_160`
  (`G_mul_coeff_ge` 13-term support sum, 13 S0 lookups, `simp [G, T1]`, `decide`);
* summary theorem `chain1_coeff_mid2 (n) (81 <= n) (n <= 160)` (`interval_cases`);
* helper lemmas `R0_coeff_eq_zero_of_gt`, `R1_coeff_eq_zero_of_gt`.
No `sorry`, no `admit`, no `native_decide`, no new `axiom`.

## Trio

* EXIT = 0
  command: `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2564Chain1Mid2Actual.olean tmp/sheaf/xif/paper/S2564Chain1Mid2Actual.lean`
  wall time: 151.15 s, no errors, no warnings (log `logs/S2564Mid2.log`).
* olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S2564Chain1Mid2Actual.olean`
  size 7,096,752 bytes
  SHA256 `70D5496179B61578CAE3F249E9B363D4AE0342A384637B75E4607E44A516AB03`
* source SHA256 `9FAA878AE428269AECD03B4B25D19C78C38F8195BB6E2970B4244CA038B4A819` (65911 bytes)
* axioms: all 175 declarations (2 R-zero lemmas + 92 S0 lookups + 80 chain lemmas +
  1 summary theorem) audited by `_S2564Mid2Verify.lean`, which imports the built
  olean and additionally type-checks the exact target statement (examples at
  n = 81, 100, 120, 160 and the Pi-type of `chain1_coeff_mid2`):
  every one depends only on `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
  Audit EXIT = 0 (log `_S2564Mid2Verify.log`, 343 lines).

## Dependencies (all previously built actual modules)

* `S2560S0ShiftedPartsActual`: R0..R7, S0_i, S0, S0_i_coeff
* `S2554Mod613ChainDataActual`: G, T1
* `S2562GmulCoeffActual`: G_mul_coeff_ge
* `S2563R0LookupActual`: R0_coeff_69 .. R0_coeff_80
* `S2563R1LookupActual`: R1_coeff_0 .. R1_coeff_79

## Notes

* For n < 613 the X^613 coefficient is 0 and deg T1 <= 11, so the left side is 0 on
  the whole range; the numerical content is `(G * S0).coeff n = 0`.
* k = 81 is the block boundary: `S0.coeff 81 = R1.coeff 0 = 240` (R0 has degree 80,
  so block 0 contributes 0 there).  The lookups needed by the 80 chain lemmas are
  exactly k = n-12 .. n for n in [81,160], i.e. k in [69,160].
* Root-level `R0` / `R1` over `ZMod 29` exist in the repository, so this module
  refers to the mod-613 blocks through transparent aliases `R0p` / `R1p`
  (`abbrev ... := S2560S0ShiftedPartsActual.R0/R1`) to avoid name ambiguity.
