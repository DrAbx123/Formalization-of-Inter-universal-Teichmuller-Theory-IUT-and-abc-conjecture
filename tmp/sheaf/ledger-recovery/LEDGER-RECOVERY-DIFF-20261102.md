# Ledger recovery proposal / diff report (Batch 0, 2026-11-02)

Status: **proposal only**. No edit was made to the main `AUDIT_LEDGER.md`.

## Objects read

- HEAD ledger: `git show HEAD:AUDIT_LEDGER.md` saved as
  `tmp/sheaf/ledger-recovery/HEAD-AUDIT_LEDGER.md`.
- Local ledger: `AUDIT_LEDGER.md`.
- Recovery directory: `tmp/sheaf/ledger-recovery/` (head-normalized/rawLF,
  damaged snapshots, frames; canonical source used here is HEAD-AUDIT_LEDGER.md).
- `coord/STATE.md` (latest entries incl. S1964/S1972/S2052 boundaries).
- `coord/reports/` recent files (S2040/S2042/S2046/S2061/S2068/S2069/S2070/
  S2093/S2094/S2100/S2103 and related).
- `coord/MAINLINE_ABC_F.md` and `coord/reports/S1449-report-ABC-graph.md`
  were already in context for object/domain/direction discipline.

## Snapshot facts (current, not the stale 917/1983 figures)

| Item | Value |
|---|---|
| local AUDIT_LEDGER.md | **938 lines**, 27A55705918EC294A790015E3A2896A19241248A6E9159CFB710196E9DED15DA |
| HEAD AUDIT_LEDGER.md | **2053 lines**, 184332 bytes, 967AFB650156BD7AD93D0334C0E48D39E0FD022ECB2BCB4039733B9E54EE4625 |
| common prefix | **first 384 lines byte-identical** |
| diff vs HEAD | **+554 / -1669** (`git diff --numstat`: 554 additions, 1669 deletions) |
| local missing history | HEAD lines **385-2053**, 1669 lines |
| local new content | local lines **385-938**, 554 lines / 97231 UTF-8 bytes |
| new headings | **77** `##` sections (S2072 through S2126, corrections/sealed/new batch) |

The earlier "917 lines / 1983-line HEAD / +533/-1669" figures are stale.
The current local snapshot is 938 lines; the HEAD object is 2053 lines. The
first 384-line identity and the 1669 deleted HEAD lines are confirmed.

## Proposal file

`tmp/sheaf/ledger-recovery/PROPOSED-AUDIT_LEDGER-20261102.md`

- **2608 lines**, 281568 bytes
- SHA256: `DE445792E12141E61D3BAC0E4F9FFF668F5894DC6989FC6964AA7C353705CC94`
- Composition:
  - lines 1-2053: exact HEAD ledger
  - line 2054: one blank separator
  - lines 2055-2608: local lines 385-938 (554 lines), appended verbatim
- Checks performed:
  - proposal lines 1-384 == HEAD lines 1-384: TRUE
  - proposal lines 1-2053 == HEAD: TRUE
  - proposal lines 2055-2608 == local lines 385-938: TRUE
  - duplicate headings among the 77 new sections: 0
  - no new heading in local tail already present in HEAD: 0

## What is restored

All HEAD lines **385-2053** (1669 lines) are restored in the proposal:
the full post-384 historical ledger, including the pre-2026-11-02 audit
history that the local file currently lacks.

## What is preserved

All local lines **385-938** (554 lines / 77 headings) are preserved verbatim
and appended after the restored HEAD history:

- S2072 corrections and affine-quotient packaging entries
- S2046/M1/M2/M3 and S2070 CardV entries
- S2087/S2088/S2089 M1/M2/M3 reductions
- S2091/S2094/S2100/S2103/S2105/S2106/S2107/S2108/S2109/S2110
- S2112/S2113/S2114/S2115/S2116/S2117/S2118/S2119/S2120/S2121/S2122
- S2124/S2125/S2126 corrections, REVIEW UNDERSTANDING SEALED, NEW BATCH
- all S2072+ lines that are currently visible in the local tail

No local S2072+ entry is dropped by the proposal.

## Append-only merge rule (proposal, not executed)

Because the local file is a truncated/reconstructed variant whose first 384
lines equal HEAD, a true append-only merge is:

1. Save a fresh backup of the current local ledger and its SHA.
2. Use HEAD lines 1-2053 as the immutable prefix (copy canonical
   HEAD-AUDIT_LEDGER.md).
3. Append **only** local lines 385-938 (554 lines), preserving their order and
   duplication/correction history; JSON/report files stay outside the ledger.
4. Do not append local lines 1-384 again (already in HEAD).
5. Do not delete/reorder HEAD lines 385-2053; future corrections are new
   appended entries referencing old lines/hashes.
6. Verify: prefix equality, tail equality, new heading count (77), no new
   heading collides with a HEAD heading, and proposal SHA above.
7. Only after review, replace the main ledger; until then keep this proposal
   in `tmp/sheaf/ledger-recovery/` and leave `AUDIT_LEDGER.md` untouched.

## Risk / caveats

- The local tail contains both original entries and later correction entries
  with overlapping S-numbers (e.g. duplicated S2072 headings, S2086/S2090/
  S2091 revisions). They are intentionally preserved, not deduplicated, so
  history remains append-only.
- "2053" is the HEAD object line count; "1983" from older reports is a stale
  line-count口径 and is not used in the proposal metrics.
- The proposal is not a verification of any S2072+ mathematical claim; it is a
  ledger recovery artifact only.

## Deliverables

- `tmp/sheaf/ledger-recovery/PROPOSED-AUDIT_LEDGER-20261102.md`
- `tmp/sheaf/ledger-recovery/LEDGER-RECOVERY-DIFF-20261102.md` (this report)
- `tmp/sheaf/ledger-recovery/_proposal_stats.txt` (raw counters/hashes)
