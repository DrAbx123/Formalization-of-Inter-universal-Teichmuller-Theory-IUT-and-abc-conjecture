> 2026-10-23 当前实施决定见 [N8 目标/输入定稿](N8-TARGET-INPUT-DECISION-20261023.md)。下文保留为历史候选；不再等待旧 A/B 选择。采用职责分层，并同步修正 native 源输入、Haar 质量、有符号体积及实际 q/输出。新 Lean 签名验收另行记录。

# C0/N8 corrected-target candidate (pending user lock)

Reason: original C0 `hull_finite ∧ hull_positive` is inconsistent (sourceHullVolume is 0 or top).

## Recommended target split

- C0 `N8TargetOutput` carries only `place : SourceInputBinding I.I` and `realization : SourceTheorem311Realization`.
- C7 actual IQ hull carries finite hull/log-volume data.
- C9 carries actual q-pilot readout and approximation; C10 full output carries q≤theta.
- No unconditional sourceHullVolume finite/positive in C0.

## Alternative

- Keep C0 hull fields but replace `hull_finite`/`hull_positive` by `SourceHullLogBound` and `qPilot_mem_hull`; remove positive-volume claim.

## Status

Pending target-lock confirmation; no Lean target file changed. Original C0 no-go remains recorded in AUDIT_LEDGER and dag/nodes/n8-s3-c0.json.