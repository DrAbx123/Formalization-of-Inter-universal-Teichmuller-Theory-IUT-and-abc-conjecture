# C9 arch audit：B_I arch ball as possible image and h_inf≥0

任务：task-363（B_I arch ball as possible image and h_inf≥0）。owner：iplsheapt。日期：2026-10-25。短审计/证明或 exact obstruction；不改 Lean/Project/目标；不引入 arbitrary r_v；只写本文件。No mixed/E3。

输入：IUT IV Thm1.10(vii)/Prop1.5(iii)(iv)（B_I-zero, π^{j+1}B_I container）；C9-ARCH-HULL-20261025.md；C9-NEW-HULL-UNIT-20261025.md（task-249）；C9-ARCH-ACTUAL-RINF-20261025.md；C9-P6TRUE-RB-HULL；C9-BI-REGION-CONSTRUCTION。

## 0. Verdict

**B_I 作为 archimedean possible image / `B_I⊂H_C,inf` 没有 source proof；`h_inf≥0` 不能推出。** IV 只给 upper container

```
H_C,inf ⊂ π^{j+1}B_I,   logvol(B_I)=0,   logvol(π^{j+1}B_I)=(j+1)logπ.
```

因为 π>1，B_I⊂π^{j+1}B_I，所以 IV 与 `B_I⊂H_C,inf` 不矛盾；但 IV 没有给这个 lower inclusion。B_I-zero 是 normalization（reference log-volume zero），不是 possible-image membership theorem。因此 `B_I⊂H_C,inf` 和 `h_inf≥0` 都是 missing source inputs。

**Conditional consequence:** 若 `B_I⊂H_C,inf`，则由 monotonicity `h_inf≥logvol(B_I)=0`；结合 b=3 B=I 的 R_B 下界 `h_C≥H_B+h_inf`（若 R_B⊂H_C）得到

```
h_C ≥ H_B = (9/41)logp = 2.067242013… > Q_p=(-3/41)logp=-0.689080671…
```

故 b=3 B=I 的 P6 成立（比 h_inf≥−S3 更强）。但这是条件性结论，前提 B_I inclusion/R_B inclusion 未证。

## 1. What IV actually gives

At level j (j+1 arch factors), IV container:

```
H_C,inf ⊂ π^{j+1}B_I.
```

B_I is the direct product of unit balls/reference balls; B_I-zero sets its normalized log-volume to0. Possible images are the images of the Theta-pilot/Gaussian data; neither B_I nor any particular sub-ball is asserted to occur as an image. The inclusion B_I⊂π^{j+1}B_I is a container containment, not a possible-image containment.

If one wants `B_I⊂H_C,inf`, one needs a source theorem that the reference ball itself is an actual possible image (or a hull whose hull contains it). The frozen source has:

```
- no actual archimedean r_v/angular term computation;
- no theorem B_I is in the possible-image family;
- no theorem H_C,inf contains the unit ball;
- only the upper container H_C,inf⊂π^{j+1}B_I and the normalization logvol(B_I)=0.
```

## 2. h_inf≥0 and b=3 P6

If `B_I⊂H_C,inf`, then

```
h_inf = logvol(H_C,inf) ≥ logvol(B_I)=0.
```

For b=3 uniform B=I, if also `R_B⊂H_C` (task-350 conditional on actual B=I/TC-B),

```
h_C ≥ H_B + h_inf ≥ H_B = 9/41 logp > Q_p = -3/41 logp,
```

so P6 holds without needing the arch lower bound `h_inf≥−S3`. The B_I ball, if actual, is a stronger positive arch input.

But the actual possible-image status is missing. No arbitrary r_v can replace it; choosing a radius large enough for B_I⊂H_C,inf would be an extra arch datum, not a source theorem.

## 3. Exact obstruction

The exact missing input is one of:

```
(A) a source theorem that B_I (or a hull region containing B_I) is an actual archimedean possible image;
(B) a direct source lower bound h_inf≥0;
(C) an actual arch hull computation showing H_C,inf contains the reference ball.
```

None is in the frozen source. IV Thm1.10(vii) gives the opposite-direction upper container; B_I-zero gives the normalization. The Theta-pilot arch definitions do not specify actual r_v/angular terms. The actual H_C,inf remains missing.

No counterexample to B_I inclusion is constructed: the source does not compute the actual arch hull, so `B_I⊄H_C,inf` is also unproved. This is a **gap**, not a disproof; the inclusion is consistent with IV.

## 4. Classification

| item | status |
|---|---|
| B_I-zero logvol(B_I)=0 | PROVED source/normalization |
| IV upper H_C,inf⊂π^{j+1}B_I | PROVED source container |
| B_I⊂π^{j+1}B_I | PROVED (π>1) |
| B_I actual possible image / B_I⊂H_C,inf | **NOT PROVED** |
| h_inf≥0 | NOT PROVED |
| B_I inclusion ⇒ h_inf≥0 | PROVED conditional monotonicity |
| B_I inclusion + R_B⊂H_C ⇒ b=3 P6 | PROVED conditional |
| actual arch r_v/angular hull | MISSING |
| counterexample B_I⊄H_C,inf | NOT CONSTRUCTED |

## 5. Conclusion

The archimedean unit ball B_I is **not proved** to be an actual possible image, and `B_I⊂H_C,inf`/`h_inf≥0` are not source theorems. IV gives only the upper container `H_C,inf⊂π^{j+1}B_I`; B_I-zero is a normalization, not membership. If B_I inclusion were supplied, monotonicity would give h_inf≥0 and, with R_B⊂H_C, b=3 B=I P6 would follow strongly. The exact obstruction is the missing actual arch hull/possible-image theorem (A)-(C); no arbitrary r_v, no mixed/E3, no Lean/Project edits; P6 open.

