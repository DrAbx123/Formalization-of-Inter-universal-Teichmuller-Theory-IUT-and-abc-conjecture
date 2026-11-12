# S2053: local CFT `PadicField` port — 19/19 modules compile

Date: 2026-11-02 (Asia/Shanghai). Workspace: `D:/lean`.

| item | value |
|---|---|
| toolchain | `leanprover/lean4:v4.32.2` (`Lean 4.32.2, commit f3b06c705e6c85f5314019d5d3baab0fec5b580c`) |
| Mathlib | pin `905b95818eb32af7874a58b427f50c1711a5e96c` |
| workspace HEAD | `9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee` (dirty tree; nothing committed by this task) |
| port root | `tmp/local-cft-port`, library `PadicField` (`lakefile.toml`: `srcDir = "tmp/local-cft-port"`) |
| pristine donor | `tmp/local-cft-port/local-class-field-theory-main/LocalClassFieldTheory/PadicField` |
| olean target | `D:/lean/.lake/build/lib/lean/PadicField/<Module>.olean` |

**Result: all 19 `PadicField` source files compile with `EXIT=0`; 19/19 oleans exist, are newer than their
sources, and load; the sources contain no `sorry`/`axiom`/`admit`/`native_decide`; all 56 sampled
declarations (at least two per module, including every headline theorem) depend exactly on
`[propext, Classical.choice, Quot.sound]`.**

This report establishes `statement_compiles` and `proof_body_checked` (kernel-checked oleans) for the
`PadicField` subtree. It does **not** claim `target_accepted`: no comparator and no paper-semantics review
were run, and the donor consumer `Duality/MuN.lean` is not ported yet (§7).

---

## 1. Per-module result

All builds use the environment of §3. "lake" rows are the S2051 project build (`lake build PadicField.<M>`,
real `--setup` plus the `lakefile.toml` leanOptions); the two new rows are the S2053 direct-lean builds of
§2. Times are wall-clock for one module.

| module | EXIT | olean bytes | olean SHA256 (prefix) | build record |
|---|---:|---:|---|---|
| `PadicField.AbsoluteInertia` | **0** | 818,448 | `93BF8FE3024F5E42…` | lake 56 s (second attempt, after stack overflow) |
| `PadicField.Complete` | **0** | 314,296 | `E360457384E56AEA…` | lake 65 s (retry after transient olean read) |
| `PadicField.Extension` | **0** | 403,056 | `56DD603F5A921273…` | lake 67 s (retry after transient olean read) |
| `PadicField.FieldNorm` | **0** | 256,064 | `B456D14C9346B1F0…` | lake 57 s |
| `PadicField.Galois` | **0** | 530,176 | `600E1406BFB27664…` | lake 61 s |
| `PadicField.Integers` | **0** | 819,016 | `50B0530A5614A023…` | lake 64 s |
| `PadicField.MaxUnramified` | **0** | 917,792 | `1F48BBABEFDD6D9A…` | lake 59 s |
| `PadicField.Norm` | **0** | 336,088 | `65481A59F51A9BF3…` | lake 57 s |
| `PadicField.PowIndex` | **0** | 1,187,040 | `0980FE662FF6683A…` | **S2053 direct lean, 83 s** |
| `PadicField.PowIndexPadic` | **0** | 361,664 | `93D824183CE62E3A…` | **S2053 direct lean, 69 s** |
| `PadicField.Powers` | **0** | 699,144 | `DD4BF620D32118E0…` | lake 58 s |
| `PadicField.Ramification` | **0** | 447,088 | `02641CD80C41D7AC…` | lake 54 s (retry after transient olean read) |
| `PadicField.Teichmuller` | **0** | 292,848 | `C8EA6D38D94994D8…` | lake 60 s |
| `PadicField.Tower` | **0** | 265,776 | `FBC51634E06A16F7…` | lake (S2051) |
| `PadicField.Uniformizer` | **0** | 551,600 | `3C527EB25A4668A4…` | lake 74 s |
| `PadicField.Unramified` | **0** | 426,408 | `2B39417854F9C96B…` | lake 59 s |
| `PadicField.UnramifiedExistence` | **0** | 1,125,088 | `10CB7B0409BDFB1E…` | lake 70 s |
| `PadicField.UnramifiedZHat` | **0** | 404,864 | `3CC8488D8F149BDB…` | lake 57 s |
| `PadicField.ZHat` | **0** | 489,176 | `6E6233881250412B…` | lake 58 s |

19/19 EXIT=0; no error was produced by any of the final attempts.

## 2. What this session added

`PowIndex` and `PowIndexPadic` were the only files without an olean.

* `PadicField.PowIndex` — direct `lean`, **EXIT=0**, 83 s, olean 1,187,040 B.
* `PadicField.PowIndexPadic` — direct `lean`, **EXIT=0**, 69 s, olean 361,664 B.
* Dependency: `PowIndex` imports `ContinuousKummerTheory.Kummer.PAdic`, which had no olean at session
  start. The relevant chain is
  `Kummer.PAdic ← Kummer.ProfiniteCompletion ← Kummer.ZHat ← Kummer.Limit ← Kummer.Equiv ← Kummer.Basic ← {ContH1.Basic, Hilbert90}`.
  `Kummer.ZHat` was built here (direct lean, EXIT=0, 73 s, 814,216 B) and `Kummer.Corestriction` was also
  built here (EXIT=0, 79 s, 617,752 B). The remaining modules of the chain were produced concurrently in
  the same `.lake` tree by another agent working in this workspace. The two available copies of the
  dependency (`tmp/local-cft-port/continuous-kummer-theory` and `…-main`) have **byte-identical `.lean`
  files (all 19 SHA256-checked)**, so the artifact corresponds to exactly the same source either way; this
  is not a source substitution. `PowIndex` compiled against that `PAdic.olean` and the final probe loaded
  it.
* Parity control: `PadicField.ZHat` was rebuilt by direct lean (EXIT=0, 72 s), then the exact lake command
  was re-run from the saved setup file
  (`lean tmp/local-cft-port/PadicField/ZHat.lean -o … --setup .lake/build/ir/PadicField/ZHat.setup.json`);
  it reproduced the S2051 lake olean **byte for byte**
  (`6E6233881250412BF480575C9D1BDD57EE1F309B7CEE348A6770F7B22BA43918`, 489,176 B). The on-disk
  `ZHat.olean` is that lake artifact.

Kummer chain artifacts consumed by `PowIndex` (final on-disk state):

| module | olean bytes | olean SHA256 |
|---|---:|---|
| `ContinuousKummerTheory.ContH1.Basic` | 631,504 | `5667742BBDD735FDB452E44E73CF8C8D221D42024D4E35B240E4985C5A781C23` |
| `ContinuousKummerTheory.Hilbert90` | 337,128 | `220780AB6E8A3E0EF937F44FC972A93021C010B91D75269E358812F4D1106949` |
| `ContinuousKummerTheory.Kummer.Basic` | 611,304 | `958ECF29800B5D8B2D9D82A6BF4888D5EA3F739C61DC897666EC0DB26B1CB65F` |
| `ContinuousKummerTheory.Kummer.Equiv` | 317,032 | `78E83D6EEF80D62000C5A439BAB593C0A265F3AC0B77B7CD60EFF90A4D8DE952` |
| `ContinuousKummerTheory.Kummer.Limit` | 1,029,160 | `E5D3D47BAFA7782C4DE32D48B203519B5E97256F5099C0F371A077D61E82E646` |
| `ContinuousKummerTheory.Kummer.ZHat` | 814,216 | `C50E8B0B2DD768552AC792CDB67CB4A603A0FFEF3F49CBEA7F1A7D7A714660BF` |
| `ContinuousKummerTheory.Kummer.ProfiniteCompletion` | 375,800 | `38ED08B178708530DF2CA1301AC4BE4EF759A58360B2F1699822C5D9E0D79E6E` |
| `ContinuousKummerTheory.Kummer.PAdic` | 770,360 | `5C8A0EA684AAAA4B91F535C2C368E4D672C0CCE4D058C0D5C420A91D6AD2B8CF` |

## 3. Command and environment

The project build is `lake`; the port used direct `lean` as requested. `LEAN_PATH` is exactly the one
lake uses for this package (order matters, `.lake/build/lib/lean` last):

```text
D:\lean\.lake\packages\Cli\.lake\build\lib\lean
D:\lean\.lake\packages\batteries\.lake\build\lib\lean
D:\lean\.lake\packages\Qq\.lake\build\lib\lean
D:\lean\.lake\packages\aesop\.lake\build\lib\lean
D:\lean\.lake\packages\proofwidgets\.lake\build\lib\lean
D:\lean\.lake\packages\importGraph\.lake\build\lib\lean
D:\lean\.lake\packages\LeanSearchClient\.lake\build\lib\lean
D:\lean\.lake\packages\plausible\.lake\build\lib\lean
D:\lean\.lake\packages\mathlib\.lake\build\lib\lean
D:\lean\.lake\build\lib\lean
```

Per file:

```text
lean -j1 -D pp.unicode.fun=true -D relaxedAutoImplicit=false -D weak.linter.mathlibStandardSet=true -D maxSynthPendingDepth=3 -R D:/lean/tmp/local-cft-port -o D:\lean\.lake\build\lib\lean\PadicField\<M>.olean D:/lean/tmp/local-cft-port/PadicField/<M>.lean
```

The four `-D` flags repeat the `[leanOptions]` of `lakefile.toml` (the values lake writes into its
`--setup` file). `-R` fixes the module prefix `PadicField.` so that `import PadicField.<M>` resolves to the
port tree. Retry loop: an attempt whose output matches `failed to read file` /
`object file … does not exist` is retried up to 5 times (10 s back-off); no source error was observed at
any point.

## 4. Axiom audit

Probe: `tmp/local-cft-port/_S2053Axioms.lean` imports **all 19** modules and runs 56 `#print axioms`
commands (2–5 per module: the headline theorem of every file plus the group-theoretic and valuation-level
lemmas they rest on). Probe exit code **0**; log `tmp/local-cft-port/_s2053_axioms_final.log`.

Every one of the 56 declarations reports exactly `[propext, Classical.choice, Quot.sound]`; there is no
`sorryAx`, no custom axiom, no `native_decide`. Inspected targets include
`PowIndex.index_range_pow_field`, `PowIndex.index_range_pow_units`, `PowIndex.index_range_pow_mul_card`,
`PowIndex.unitsProdEquiv`, `PadicField.index_range_pow`, `PadicField.card_quot_natCast`,
`PadicField.galMaxUnramifiedEquiv_frobUr`, `PadicField.zhatPow_frobUr_surjective`,
`PadicField.absInertia_eq`, `PadicField.unramifiedQuotientEquiv_arithFrob`,
`PadicField.exists_isUnramified`, `PadicField.exists_limit`, `PadicField.nrm_mul`,
`Brauer.zhatPow_surjective`, `Teichmuller.teichmuller_pow_Q`.

```text
'PadicField.nrm_sub_le_of_le_geometric' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.exists_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.Integers.smul_top_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.nrm_algEquiv_tower' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.Integers.coe_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.finiteDimensional_tower' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.v_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.nrm_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.nrm_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.residueGalEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.card_gal_residue' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.orderOf_frob' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.isCyclic_gal' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.nrm_add_le_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.nrm_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.exists_pow_eq_one_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.exists_pow_eq_of_nrm_sub_one_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.wval_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.Integers.nrm_coe_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.v_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.nrm_le_iff_v_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.Integers.maximalIdeal_eq_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'PowIndex.unitsProdEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'PowIndex.relIndex_onePlus' depends on axioms: [propext, Classical.choice, Quot.sound]
'PowIndex.index_range_pow_mul_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'PowIndex.index_range_pow_units' depends on axioms: [propext, Classical.choice, Quot.sound]
'PowIndex.index_range_pow_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.e_mul_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.f_mul_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.exists_monic_irreducible_residue' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.finrank_unramifiedOfDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.exists_isUnramified' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.IsUnramified.f_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.IsUnramified.eq_unramifiedOfDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.maxUnramified_eq_iSup_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.exists_le_unramifiedOfDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.dense_zpowers_frobUr' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.absInertia_apply_eq_of_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.absInertia_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.unramifiedQuotientEquiv_arithFrob' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.arithFrob_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.galMaxUnramifiedEquiv_frobUr' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.zhatPow_frobUr_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.isGalois_of_isUnramified' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.teichmullerSet_pow_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'Teichmuller.teichmuller_pow_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'Teichmuller.eq_teichmuller' depends on axioms: [propext, Classical.choice, Quot.sound]
'Brauer.zhatPow_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Brauer.zhatPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Brauer.zhatPow_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Brauer.limEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Brauer.denseRange_intToZHat' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.card_quot_natCast' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.v_natCast' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.q_eq_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.index_range_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 5. No source edits

The 19 files differ from the pristine donor only in the rewritten import roots (so that
`LocalClassFieldTheory.PadicField.X` becomes `PadicField.X`). `git diff --no-index --numstat`:

| file | added/deleted lines | note |
|---|---:|---|
| AbsoluteInertia, Complete, Extension, FieldNorm, Galois, Integers, MaxUnramified, Powers, Ramification, Tower, Uniformizer, UnramifiedExistence | 1/1 | one `import` line |
| UnramifiedZHat | 2/2 | two `import` lines |
| Unramified, PowIndexPadic | 3/3 | three `import` lines |
| Norm, PowIndex, Teichmuller | 0/0 | byte-identical to donor |
| ZHat | 0/0 | byte-identical to donor `Galois/ZHat.lean` |

No mathematics was changed, no statement weakened, no axiom added. `grep` over
`tmp/local-cft-port/PadicField/*.lean` for `sorry|admit|native_decide|^axiom |sorryAx` returns 0 hits.

## 6. Artifact manifest (full hashes)

```text
module                         src SHA256                                                        olean SHA256
PadicField.AbsoluteInertia     D3C2726060F73FBDB1D7CAE69A5174A27E1965E5F07DF83A181E6DBEF3FA3B38  93BF8FE3024F5E42B4F0DA3CB0D0E2C94D075AF725A6D181FA70C8180C771540
PadicField.Complete            5AA9C763FBDF4FA1DD2B60B9405F66FC5B00CF872F06862CA4738BDE47D50024  E360457384E56AEA73A73D0AC986C56ED743958D5DC29313368F72270CC52049
PadicField.Extension           E4955995C9190EB7688E028300199C03ED1938F71591982544A9E60DBD999429  56DD603F5A92127368CD940BA8021046FCBF5C87F14D080D179A737B3FE336EA
PadicField.FieldNorm           8AFD0083C2C2C46B3366EFC0974413B236B73E6F5E6FABDB6669DCF8EAFD37BB  B456D14C9346B1F0BC905C4A1C8763FB34DA2DFFC3408382E5C2ED661F0349D4
PadicField.Galois              B4FD8F4E587DE25FB611505B145F7C5E29A300FBFABB7EEC0526A90472058DDE  600E1406BFB27664456B194E5D75A308E25478D13CB77EC4BE8BF3B46699383F
PadicField.Integers            E843AB4D003D6FD769585686043381D82F52FF97C419CF6DAFD7A320DD25EED4  50B0530A5614A023BF50548809E943DF9D55E1EFA614315B43016AC3E0C3887F
PadicField.MaxUnramified       417197801DD5DCE57E3A9F17D9E828485A57FA7AE0F90D420AE7BAC92B9B4C1D  1F48BBABEFDD6D9A999AE5FDD9E6B937468B1C7A88341D5FAC8A34BE9EF7F0B5
PadicField.Norm                AD07ABC7A1158ABC8532B651342ED2BACB1843EAAB6C8C65F5C86288A4328A8D  65481A59F51A9BF3952E7CFED90196DCF81846CC28ACB2E4E09CBA8C1EE90E26
PadicField.PowIndex            2BE91E1A4B549AD6177FA298368122C39A66F5C1A5DD9A94AAEC7C0490CF8E11  0980FE662FF6683A0E19FC2785C620951948C0E183106F92A8E94799B2224413
PadicField.PowIndexPadic       B59FA6C3421DB87A8650801EC294A26A0845463346683243A6BD0DDDB8C24E88  93D824183CE62E3A714ADFC3A8FE8D389B1D6DC860C36BD8773C25BCB66E25DC
PadicField.Powers              45CF82FDB9F55D3832B0422BCC8EF3F2E0AA03FB6DF8E19C0986FBB9835EFAFF  DD4BF620D32118E0C7C0E1CB7AA9041828941D11E88A0A20EA44894428351677
PadicField.Ramification        F1D9B4172014773DDCAA21C730D68EBEF0FF12B36C7E1143D85F834C6E0FA77E  02641CD80C41D7AC8A735F02284C831C76C1E8E205E04E79A8F36BC45F137873
PadicField.Teichmuller         B91F7E475A08BC7681E866DD7A5C0F3A05191732909143667DFC1C7D91FC36A7  C8EA6D38D94994D84F578A1F9328CEDB3C542C3D0F3E4C304201B2B55DF741AD
PadicField.Tower               0D4693228E86E11140B80DB2FD2A64F945020FF59DBAA367A0B6145DCF1D60AF  FBC51634E06A16F7C9BF33B36364F832BA783B566D560D8B6E0A4DFC3168130D
PadicField.Uniformizer         6493EF3E92B1FA6D39EFD86CE7B0EF3E3C2047D21E678D657B6B0CD0B24ED3B7  3C527EB25A4668A43822F1A49B8CE841A3C19A921B654A211644F051BA58234D
PadicField.Unramified          1ED65FB94B950FDD08E73E9BEC0C89946CCD323529BC2BF829410F6263D4A222  2B39417854F9C96BD30D3318290C758D3130047F7C4EAD36D1F3941EC2709D8A
PadicField.UnramifiedExistence EF111E2506B9A15BDEE611F5E81EE842249462A8034B7576103A6E5DBDC5AEE7  10CB7B0409BDFB1EBF0BC63F221EA3E669E5C5CDCB1DDA4029F95239A1130A47
PadicField.UnramifiedZHat      EC57A62615C12A9792A5049326D13F91481504F17DECD695D8E64B78DB069EDC  3CC8488D8F149BDB96D038127EA7702E68D8DB106BFED580C4B71DA81765389A
PadicField.ZHat                6481AAF802BE16489C90305283BCA51EA6C78C970BF67AB88082AA4EAAD0FFB1  6E6233881250412BF480575C9D1BDD57EE1F309B7CEE348A6770F7B22BA43918
```

## 7. Scope, caveats, and what is not claimed

* **Compilation only.** `statement_compiles` and `proof_body_checked` hold for all 19 modules; the oleans
  were produced by the kernel. No `target_accepted` claim (no type-comparator, no source-semantics review
  in this task).
* **Consumer status.** In the donor tree, `LocalClassFieldTheory/Duality/MuN.lean` (line 7 imports,
  line 395 uses `index_range_pow`) is the consumer of `PowIndexPadic` — the local Euler-characteristic
  input for the `μ_n`-duality. The `Duality` subtree is **not** part of the current port, so
  `PowIndex`/`PowIndexPadic` are leaves today. The other 17 modules are consumed by `Reciprocity/*` and
  `ClassFieldAxiom/*` (e.g. `Reciprocity.Artin` ← `PadicField.AbsoluteInertia`,
  `Reciprocity.GaloisStructure` ← `PadicField.UnramifiedZHat`,
  `ClassFieldAxiom.Approximation` ← `PadicField.Complete`).
* **Build artifacts.** Direct `lean` writes only the `.olean`; it does not write `.ilean`, `.trace` or
  `.olean.hash`, so a later `lake build` re-derives its own artifacts (the 17 lake rows already carry
  lake's `.olean.hash` from S2051). A direct-lean olean is not byte-identical to lake's for the same
  source (ZHat: 489,080 B vs 489,176 B); the difference is caused by lake's `--setup` build metadata, not
  by the source — the §2 control run with lake's `--setup` file reproduced lake's bytes exactly, and the
  probe loads both variants with identical results.
* **Transient reads.** Earlier S2051 lake builds and one attempt in this session logged
  `failed to read file …olean.private` (other processes were writing the same tree); every such failure was
  retried and is not a source error. During this session a sibling agent was concurrently building the same
  Kummer modules into the same `.lake` tree; the final probe was run after the last write and passes.
* **Timings** are one-shot wall-clock on a shared 24-core machine and are not a build benchmark.

## 8. Reproduction

```powershell
# oleans for the two new modules (plus the ZHat parity control); the other 17 are `lake build` rows
& D:\lean\tmp\local-cft-port\_s2053_final.ps1
& D:\lean\tmp\local-cft-port\_s2053_pow.ps1
# axiom probe
$env:LEAN_PATH = '<the list of §3 joined with ;>'
lean -j1 -D pp.unicode.fun=true -D relaxedAutoImplicit=false -D weak.linter.mathlibStandardSet=true -D maxSynthPendingDepth=3 -R D:/lean/tmp/local-cft-port D:/lean/tmp/local-cft-port/_S2053Axioms.lean
```

Logs: `_s2053_final.tsv`, `_s2053_final.raw.log`, `_s2053_pow.tsv`, `_s2053_axioms_final.log`,
`_s2053_manifest.json`, `_s2053_kummer.json`; backup of the 19 pre-session oleans in
`_s2053_olean_backup/` (under `tmp/local-cft-port/`).
