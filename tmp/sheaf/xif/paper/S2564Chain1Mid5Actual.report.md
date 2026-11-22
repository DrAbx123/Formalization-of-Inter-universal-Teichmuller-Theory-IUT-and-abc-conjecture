# S2564Chain1Mid5Actual — report (2026-11-05)

Range: n in [321, 400].
Target: `((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n`.

Deliverable: `tmp/sheaf/xif/paper/S2564Chain1Mid5Actual.lean` (1122 lines, 58216 bytes).
Contents:
* 92 S0 lookups `S0_coeff_309` .. `S0_coeff_400` (S0 expanded into its 8 shifted
  pieces, `S0_i_coeff` if-conditions, active block read off `R3_coeff_*` / `R4_coeff_*`,
  inactive blocks killed by degree bounds R0: 80, R1/R2/R3: 79);
* 80 target lemmas `chain1_coeff_321` .. `chain1_coeff_400`
  (`G_mul_coeff_ge` 13-term support sum, 13 S0 lookups, `simp [G, T1]`, `decide`);
* helper degree-bound lemmas for R0 .. R3.
No `sorry`, no `admit`, no `native_decide`, no new `axiom`.

## Trio

* EXIT = 0
  command: `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2564Chain1Mid5Actual.olean tmp/sheaf/xif/paper/S2564Chain1Mid5Actual.lean`
  wall time: 180.34 s, no errors, no warnings (log `_S2564Mid5Compile.log`).
* olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S2564Chain1Mid5Actual.olean`
  size 7,141,704 bytes
  SHA256 `E3C11DA4368714FD077066E0300AC978C47FA8DFCC236F4B90DC7740402FD07D`
* source SHA256 `3DD70B71644F098150DF1C623BD9D508A5FD77F8E277957172B95DEDA77E1BAD` (58216 bytes)
* axioms: all 180 declarations (92 S0 lookups + 80 chain lemmas + 4 R-zero lemmas +
  4 R-degree lemmas) audited by a scratch module importing the built olean:
  every one depends only on `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
  Audit EXIT = 0 (log `_S2564Mid5Axioms.log`).

## Dependencies (all previously built actual modules)

* `S2560S0ShiftedPartsActual`: R0..R7, S0_i, S0, S0_i_coeff
* `S2554Mod613ChainDataActual`: G, T1
* `S2562GmulCoeffActual`: G_mul_coeff_ge
* `S2563R3LookupActual`: R3_coeff_68 .. R3_coeff_79
* `S2563R4LookupActual`: R4_coeff_0 .. R4_coeff_79

## Notes

* For n < 613 the X^613 coefficient is 0 and deg T1 <= 11, so the left side is 0 on
  the whole range; the numerical content is `(G * S0).coeff n = 0`.
* k = 321 is the block boundary: S0_3 contributes R3.coeff 80 = 0 (deg R3 <= 79),
  so S0.coeff 321 = R4.coeff 0 = 232.
* Root-level R0..R7 over ZMod 29 exist in the repository, so the mod-613 blocks are
  always referenced as `S2560S0ShiftedPartsActual.Ri`.
