# AUDIT_LEDGER recovery artifacts (2026-11-01, S1977)

## What happened

At 2026-11-01T18:53 (Asia/Shanghai) the S1977 worker appended its package entry
to D:\lean\AUDIT_LEDGER.md.  It read the file with the DSH `read` tool, which
returned only the **first 385 lines** of the then-current 722-line working copy
(approximately a 50 KB output cap), and wrote `existing + new entry` back.
That overwrote the uncommitted part of the ledger (working-copy lines 386-722).

## What was lost

The committed ledger (commit 61951cd0, git show HEAD:AUDIT_LEDGER.md) has 2053
lines and ends at the 2026-08-07 entries.  The working copy was a 722-line
version = committed lines 1-384 + 2026-10/11 entries (starting with
`## 2026-11-01 S1894 ...`).  Lost: working-copy lines 386-659 (section bodies of
the 2026-10/11 entries).  Their section headers survive in DSH session
transcripts, but not their bodies.

## What was recovered (in this directory)

- AUDIT_LEDGER.damaged-20261101T1853.md — the damaged 432-line file as written
  by S1977 (before repair).  Kept for the record.
- AUDIT_LEDGER.head-rawLF.md / AUDIT_LEDGER.head-normalized.md — the committed
  version (git show HEAD:AUDIT_LEDGER.md, normalized to LF).
- recovered-lines-660-719.txt — numbered lines 660-719 of the lost working copy,
  recovered verbatim from a DSH session transcript (a tail read of
  AUDIT_LEDGER.md at offset 660, in
  ledger-reads/read-e6494dfe-62-f6cab52be91a.json).
- recovered-lines-660-722.txt — the same fragment with the three closing lines
  720-722 (from the worker's earlier `Get-Content -Tail 60` output, which
  covered lines 663-722).
- ledger-reads/*.json — all DSH session frames that mention AUDIT_LEDGER.md,
  extracted from %USERPROFILE%\.dsh\sessions (frames are single zstd frames of
  session.v4.jsonl.zstd).

## Repair performed

AUDIT_LEDGER.md was rewritten as:

1. the committed version (exact, 184332 bytes),
2. a repair note documenting the damage,
3. the recovered lines 660-722 (verbatim, labelled),
4. the S1977 entry.

## What still has to be restored by the maintainer

Working-copy ledger lines 386-659 (2026-10/11 entry bodies, from S1894 up to the
entry whose tail is reproduced).  Candidate sources:

- `coord/reports/*.md` (per-package reports; e.g.
  coord/reports/S1942-prepsi-five-actual.md),
- `tmp/sheaf/xif/paper/logs/S*_report.md`,
- DSH session transcripts (`%USERPROFILE%\.dsh\sessions\--D-lean--\*\session.v4.jsonl.zstd`;
  multi-frame zstd, decompress frame by frame at offsets of 28 b5 2f fd);
  the section headers \`## 2026-...\` of the missing entries are present there,
  the bodies only for some entries.

## Safe append recipe (do not repeat the damage)

Never use the DSH `read` tool output as the whole file.  Append instead, e.g.

    node -e "require('fs').appendFileSync('D:/lean/AUDIT_LEDGER.md', text, 'utf8')"

or PowerShell `Add-Content -Path ... -Value ... -Encoding utf8NoBOM`, or read the
file with `fs.readFileSync` (which is not truncated) before rewriting.
