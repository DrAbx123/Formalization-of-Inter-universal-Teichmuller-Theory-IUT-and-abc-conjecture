# EXPLORATION-C-C1 — local-term calculator (e=1 corrected, Sage local data)

Status: **NUMERIC / MODEL** (model data, not a theorem) — **PARTIAL** (C1 not exact).
A926 upgrade: Ind2/archDefect now paper-MODEL instance; batch margin on C2 4154 curves in `coord/c1_margin_v2.csv`.
Route/stage: 路线 C, 阶段 C1.
Date/author: 2026-11-12; lane hull.
Version pins: lana root tree only, `Iut/WallEquiv/VcI.lean:844` (`hullPacket_tame`),
`:806` (`hullPacket_finite`), `:741` (`logVol_hull_vcI_eq`); Sage 10.9
(WSL Ubuntu-24.04, `/opt/miniconda/envs/sage/bin/sage`); Python 3 (`python -X utf8`).

## 1. 做了什么

- Code: `tools/c1_calculator.py`; Sage helper: `tmp/c1_sage_local.sage`;
  measured data: `coord/c1_sage_raw.json`; sample: `coord/c1_sample.csv`.
- Commands:
  - `python -X utf8 tools/c1_calculator.py` (smoke);
  - `python -X utf8 tmp/c1_run.py` (20-row table + CSV);
  - `wsl -d Ubuntu-24.04 -e bash -lc '.../sage /mnt/d/lean/tmp/c1_sage_local.sage > .../coord/c1_sage_raw.json'`.
- Read-only sources: `Iut/WallEquiv/VcI.lean:464` (`logShellRadius`),
  `:689` (`hullPacket`), `:806` (`hullPacket_finite`), `:844` (`hullPacket_tame`),
  `:741` (`logVol_hull_vcI_eq`); `Iut/Concrete/LocalConstruct/LocalLogShell.lean:41`
  (`logShell` with `(2p)^-1`).
- **A917 correction**: semistable multiplicative bad p not in {2,3,ell} has e=1,
  hence H_v = (1-1/e)log p = 0 (consistent with `hullPacket_tame` at unramified p).
- p=2,3: Sage `E.local_data(p)` gives reduction type / conductor exponent; e estimated
  as p^(conductor_exp) (**MODEL**), H uses (1-1/e)log p.
- p=ell: marked bad/rejected.
- Infinity: arch = log(sqrt2*pi) = 1.491303 (C0 placeholder).
- T_v = (sF-1)*ord_p(q)*log p/(2l), sF=(nC+1)(2nC+1)/6; ord_p(q)=v_p(Delta) only
  at multiplicative p; 0 at additive/good.
- Ind2_v = sum_{j=1..nC} frac(j^2 ord_p(q)/(2l)) log p (C0 tentative).
- M = sum H + sum Ind2 - sum T.
- Admissibility: ell prime > 3, ell not bad, ell does not divide ord_p(q).
  p=2,3 are kept as special measured places (deviation registered in §3.3).

### 1.1 试金石（defer）

本阶段不主张不等式（C1 是数据/计算器阶段）。试金石仅在其数据被 A3/B1/C3
定理化时适用，届时在相应主张中回答 Q1–Q4；此处显式 defer，不主张 3^k−1 信息。

## 2. 数据表

### 2.1 20 条 Frey 曲线（ell=5, nC=2, l=5）

每行 label: **MODEL**（V/T/Ind2/M 均为模型量；Delta、坏位、admissible 是
**NUMERIC** 输入）。样本：`(1,2^k-1,2^k)`、`(1,3^k-1,3^k)`, k=2..11；
剔除规则：ell=5 为坏位则拒绝（3 条）。

| base | k | |Delta| | bad | V | T | Ind2 | M | admissible | p=2,3 data | label |
|---:|---:|---:|---|---:|---:|---:|---:|---|---|---|
| 2 | 2 | 2304 | 2 3 | 2.8302 | 0.0000 | 0.0000 | 2.8302 | yes | p2:e~8,Sage_add; p3:e~3,Sage_mult | MODEL |
| 2 | 3 | 50176 | 2 7 | 2.0978 | 0.5838 | 1.9459 | 3.4599 | yes | p2:e~8,Sage_add | MODEL |
| 2 | 4 | 921600 | 2 3 5 | 3.8578 | 0.4828 | 1.6094 | 4.9844 | NO: ell is bad | p2:e~2; p3:e~3,Sage_mult | MODEL |
| 2 | 5 | 15745024 | 2 31 | 1.8379 | 1.0302 | 3.4340 | 4.2417 | yes | p2:e~2,Sage_mult | MODEL |
| 2 | 6 | 260112384 | 2 3 7 | 2.5703 | 0.5838 | 1.9459 | 3.9324 | yes | p2:e~2,Sage_mult; p3:e~3,Sage_mult | MODEL |
| 2 | 7 | 4228120576 | 2 127 | 1.8379 | 1.4533 | 4.8442 | 5.2288 | yes | p2:e~2,Sage_mult | MODEL |
| 2 | 8 | 68183654400 | 2 3 5 17 | 3.8578 | 1.3328 | 4.4427 | 6.9677 | NO: ell is bad | p2:e~2,Sage_mult; p3:e~3,Sage_mult | MODEL |
| 2 | 9 | 1095220854784 | 2 7 73 | 1.8379 | 1.8709 | 6.2364 | 6.2033 | yes | p2:e~2,Sage_mult | MODEL |
| 2 | 10 | 17557843083264 | 2 3 11 31 | 2.5703 | 1.7496 | 5.8319 | 6.6526 | yes | p2:e~2,Sage_mult; p3:e~3,Sage_mult | MODEL |
| 2 | 11 | 281200165912576 | 2 23 89 | 1.8379 | 2.2872 | 7.6241 | 7.1748 | yes | p2:e~2,Sage_mult | MODEL |
| 3 | 2 | 82944 | 2 3 | 2.8735 | 0.0000 | 0.0000 | 2.8735 | yes | p2:e~16,Sage_add; p3:e~3,Sage_mult | MODEL |
| 3 | 3 | 7884864 | 2 3 13 | 2.8952 | 0.7695 | 2.5649 | 4.6907 | yes | p2:e~32,Sage_add; p3:e~3,Sage_mult | MODEL |
| 3 | 4 | 671846400 | 2 3 5 | 4.1611 | 0.4828 | 1.6094 | 5.2877 | NO: ell is bad | p2:e~16,Sage_add; p3:e~3,Sage_mult | MODEL |
| 3 | 5 | 55330330176 | 2 3 11 | 2.8952 | 1.4387 | 2.3979 | 3.8544 | yes | p2:e~32,Sage_add; p3:e~3,Sage_mult | MODEL |
| 3 | 6 | 4506483631104 | 2 3 7 13 | 2.8735 | 1.3533 | 4.5109 | 6.0311 | yes | p2:e~16,Sage_add; p3:e~3,Sage_mult | MODEL |
| 3 | 7 | 365694024504384 | 2 3 1093 | 2.8952 | 2.0990 | 6.9967 | 7.7929 | yes | p2:e~32,Sage_add; p3:e~3,Sage_mult | MODEL |
| 3 | 8 | 29639285965209600 | 2 3 5 41 | 4.1611 | 1.5969 | 5.3230 | 7.8872 | NO: ell is bad | p2:e~16,Sage_add; p3:e~3,Sage_mult | MODEL |
| 3 | 9 | 2401270151831194176 | 2 3 13 757 | 2.8952 | 2.7583 | 9.1943 | 9.3312 | yes | p2:e~32,Sage_add; p3:e~3,Sage_mult | MODEL |
| 3 | 10 | 194516058884472382464 | 2 3 11 61 | 2.8735 | 2.6720 | 6.5088 | 6.7103 | yes | p2:e~16,Sage_add; p3:e~3,Sage_mult | MODEL |
| 3 | 11 | 15756156545501746903104 | 2 3 23 3851 | 2.8952 | 3.4175 | 11.3916 | 10.8693 | yes | p2:e~32,Sage_add; p3:e~3,Sage_mult | MODEL |

CSV: `coord/c1_sample.csv`.  NUMERIC inputs: Delta, bad prime sets, admissibility;
MODEL: V, T, Ind2, M, wild e estimates.

### 2.2 外部登记表 E-C1

| EID | 陈述 | 来源 | 验证级别 |
|---|---|---|---|
| EXT-C1-1 | `hullPacket_tame`: at tame p, hullPacket = sum_c w_c sum_j (1-1/e_cj) log p | lana root `Iut/WallEquiv/VcI.lean:844` | LITERATURE/UNVERIFIED (no olean) |
| EXT-C1-2 | scale factor in log-shell: `logShell = (2p)^-1 log(1+m)` | root `Iut/Concrete/LocalConstruct/LocalLogShell.lean:41` | LITERATURE/UNVERIFIED |
| EXT-C1-3 | arch constant C0 placeholder `log(sqrt2*pi)` | C0 pending; model value | MODEL/UNVERIFIED |
| EXT-C1-4 | local reduction type / conductor exponent at p=2,3 | Sage 10.9 `E.local_data(p)`; output `coord/c1_sage_raw.json` | NUMERIC (external calculation) |
| EXT-C1-5 | wild e estimate `e = p^conductor_exp` | this work | MODEL (not a theorem) |

### 2.3 偏离登记（ROUTES 规则 4：坏位为奇）

| 偏离 | 内容 | 理由/影响 |
|---|---|---|
| DEV-C1-1 | p=2,3 kept in sample although 2/3 divide Delta for all Frey curves; p=2,3 not dropped | literal rule would reject the whole Frey family; they are treated as special measured places (Sage), not as ordinary bad places; affects admissibility count |
| DEV-C1-2 | wild e model `p^conductor_exp` | exact wild local term unavailable; marked MODEL |


### 2.4 A926 paper-MODEL upgrade

- `ind2_term(j, vp_q, l, p) = frac(j^2 vp_q/(2l)) log p` (paper form; label MODEL-PAPER).
- `arch_defect(N) = log((2^(N-1))!)/2^N` (paper-MODEL; `math.lgamma`);
  N convention from `Iut/WallEquiv/Gap.lean:66`: packet of N complex factors;
  lana `Iut/Concrete/LocalEstimate.lean:334`: `Fintype.card (Lab i) = i.1+2`,
  so for capsule i (0-indexed), N = i+2; we average over capsules:
  `arch = (1/nC) sum_i arch_defect(i+2)` (l=5,nC=2 => (arch_defect 2 + arch_defect 3)/2).
- p=2,3 remain Sage-measured reduction/type + MODEL H; odd semistable bad p: e=1, H=0.
- Batch: `python -X utf8 tools/c1_batch.py` reads `data/c2_invariants.jsonl`,
  writes `coord/c1_margin_v2.csv` columns `N,label,nbad,M,admissible`.

### 2.5 Batch distribution (C2, 4154 curves, l=5, paper-MODEL)

| metric | value | label |
|---|---:|---|
| total curves | 4154 | NUMERIC |
| admissible | 2604 | MODEL (ell=5, ell not bad, 5 not | vp) |
| M < 0 | 74 | MODEL |
| min M | -5.5702 | MODEL |
| q01 / q05 / q25 / q50 | -0.5656 / 0.8847 / 2.2020 / 2.7914 | MODEL |
| q75 / q95 / q99 | 3.3617 / 4.6003 / 5.3408 | MODEL |
| max M | 5.5921 | MODEL |

Negative samples (first 10, label/model M): 11a1 -0.3142, 38b2 -0.1043,
58b2 -0.2100, 66c4 -2.2326, 118b2 -0.3875, 155a2 -0.5732, 158c2 -0.4605,
210a7 -0.1925, 210b8 -0.1925, 210e8 -1.3600.  These are MODEL negatives, not
counterexamples to any theorem; they may indicate the model/arch factor is too small.

### 2.6 External additions (A926)

| EID | 陈述 | 来源 | 级别 |
|---|---|---|---|
| EXT-C1-6 | `archDefect = log((2^{N-1})!)/2^N` (paper shape, N complex factors) | lana root `Iut/WallEquiv/Gap.lean:66` | LITERATURE/UNVERIFIED |
| EXT-C1-7 | `N = card(Lab i) = i.1+2` | lana root `Iut/Concrete/LocalEstimate.lean:334` | LITERATURE/UNVERIFIED |
| EXT-C1-8 | C2 JSONL 4154 semistable curves | `data/c2_invariants.jsonl` (Sage 10.9/Cremona; C2 doc) | NUMERIC |

## 3. 与判定条件的对照

- C1 通过条件：计算器 + ≥20 条手算曲线核对一致；admissibility 已实现；偏离规则已登记。
- 本交付满足：计算器、20 条核对、admissibility、偏离登记。
- 但 C1 exactness 条件不满足：H at p=2,3 是 MODEL；arch/Ind2 是 C0 占位；wild
  logShellRadius 未实现。
- 明确判定：**PARTIAL**（核对完成、模型计算器交付；A926 paper-MODEL 升级完成；非 exact，不能进入 C2/C3 作为定理依据）。
- A926 batch: 4154 C2 curves, 2604 admissible, 74 model-negative M; no signal claimed.

## 4. 下一步 / 停止

1. C0 精确化 archDefect 与 Ind2（owner: hull/C0；判定点：两条都有结论）。
2. wild p=2,3 的 logShellRadius/local term 实现（owner: hull；判定点：p=2,3 项可复现且非 MODEL）。
3. 之后才允许 C2/C3 搜索（owner: 待定；判定点：C2 字段齐全、C3 零违例关系过试金石）。

当前 STOP 于 C1：**没有信号**（M>0 仅是模型数，不构成任何不等式证据）。
