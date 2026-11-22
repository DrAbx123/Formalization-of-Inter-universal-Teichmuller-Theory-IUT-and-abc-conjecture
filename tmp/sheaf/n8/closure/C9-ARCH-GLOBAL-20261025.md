# C9：实际 archimedean 读出与全局补偿（stage1）

任务 ID：task-156 / C9-ARCH-GLOBAL-20261025；owner：primespine；日期：2026-10-25。
消费者：n8-c9-output-region-source-route 的 P6；SHEAF stage1。
性质：自然语言研究；不改 Lean/Project，不改目标，不新增任意假设，不伪造全局闭合。

## 0. 输入、纠偏与状态

冻结输入：

- C9-TAME-LOG-DOMAIN-20261025.md（TAME），SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06。
- C9-GLOBAL-ASSEMBLY-20261025.md（task-151），SHA256 6ab115790d8cdfd9e261985f7f209e4817c572af6aaf4a48eb0efdc2de52ccf2。
- C9-UNIFORM-HULL-20261025.md（task-148），SHA256 2bf7a8c4d61ed142d9699e2cec8b8ccad8407c4c274e2cb1ca16f6effcf695fa。
- C9-LOG-DOMAIN-EXTEND-20261025.md（task-146），SHA256 cc52a8cf0d5fb56172a7af2f6fb0c5c57eb726a5a459d3ccde42fddd3daf2dfa。
- C9-SYMPLECTIC-SOURCE-20261025.md（task-147），SHA256 3f98f68a5e143dcd51ed6790b1c839ae7b8811e4e418d48b02e37e7c4d5b9c70。
- C9-IND1-GLOBAL-20261025.md（task-149），SHA256 94785726ee890f6bc672861c570238f040636a6273a7722b2621949c48af9ab8。

两次纠偏必须同时生效：

1. task-147：TAME §2 的辛 donor 不能按原文当作实际定理。rho 不已知为群同态，无同态截面；正确对象是闭子群 H=Phi^{-1}(Sp_{2g}(Z_p))，不是 rho 的像；boundary-word 自由群替换不全是实际 Galois 自同构，实际来源是 mapping-class rho/Dehn twists；2025 trace basis 与 2026 symplectic basis 的同一性只是推断；trace 是 Tr_{k/k^{(d=1)}}，只在 tame totally ramified、k^{(d=1)}=Q_p 时等于 Tr_{K/Q_p}；J=m、标准 lattice 分类、轨道生成 (T7) 和体积增量 (T8) 是推断后果，不是 Kondo 定理。
2. task-149：TAME (11)-(14) 不是目标证明。完整 Ind1 是 procession 自同构群，不是有限 label translation；把环同构 F 直接用于 F(Hull(...)) subset H_C 无效。目标容器需 TC-A 到 TC-H，以及使用修正辛 donor 的 TC-S。所有下游 target-containment 必须标为条件或撤回。

因此本文把 task-151 的有限 deficit D_p^Sp 标为 conditional/inferred，不把 TAME (14)/(15) 当作实际 finite lower bound。archimedean 局部公式本身是源级实际数据；但“补偿 finite deficit”是条件命题，依赖 finite donor 修正和目标容器条件。

## 1. 实际 archimedean 局部对象与读出公式

固定完整 C、基域 F=F_mod、n=[F:Q]。对 v|infty，F_v 是 R 或 C；d_v=[F_v:R]（实 1，复 2）。IUT III Remark1.2.2(ii)（p.36）在复 archimedean 域给出 log-shell

    I_v = { a in F_v : |a|_v <= pi }.                         (A1)

IUT III Def1.1(ii)/(vii) 与 Prop1.2(iii),(v) 把 archimedean 读出分为 angular log-volume（单位圆/角向）和 radial log-volume（|.| 的径向），并证明它们与 log-link 相容；AbsTopIII Prop5.7(ii)、Cor5.10(ii) 给出实际 archimedean log-volume。本文只使用这些源接口和标准径向体积，不重证 AbsTopIII。

### 1.1 径向球公式

对径向球 B_v(r)={a in F_v : |a|_v <= r}，以 I_v（半径 pi）为参考、单位球 Haar 质量归一化，实际 radial log-volume 为

    h_v^rad(B_v(r)) = d_v * log(r/pi).                        (A2)

推导：F_v=R 时长度比 (2r)/(2pi)=r/pi，d_v=1；F_v=C 时面积比 (pi r^2)/(pi pi^2)=(r/pi)^2，d_v=2。径向环带 {r1<=|a|<=r2} 的读数是 d_v(log(r2/pi)-log(r1/pi))。非径向区域还要加角向项 h_v^ang；本文的补偿判据只对径向 hull 写成单一半径，非径向时必须保留 (A13) 的两项，不能压成一个数。

### 1.2 全部 infinite places 的读出版本

令 r_v=sup{|x|_v : x in H_C 的 archimedean 分量}（hull 径向投影半径）。对径向 archimedean hull，

    h_inf(C) = sum_{v|infty} alpha_v * log(r_v/pi),           (A3)
    alpha_v = d_v/[F:Q],   sum_{v|infty} alpha_v = 1.         (A4)

alpha_v 与有限处的 alpha_p=[(F_mod)_p:Q_p]/[F_mod:Q] 使用同一 degree normalization。F=Q 时只有一个实地方，alpha_inf=1，于是

    h_inf(C) = log(r_inf/pi).                                 (A5)

公式 (A3) 是实际 archimedean 读出的精确模板；r_v 必须来自完整 C 的实际输出 hull。本文没有构造完整 C，因此不能给 r_v 数值；不能令 r_v=1，也不能把 h_inf 设为 0。r_v=pi 只是 shell 边界，不是实际半径。

## 2. 全局权重与 h_C 的分解

按 III Rmk3.1.1(ii)、Prop3.9、IV Thm1.10(vii) 的 degree normalization：

    h_C = sum_{p in S_bad} alpha_p h_p + sum_{p in S_good} alpha_p h_p + h_inf(C),   (A6)
    Q_C = sum_{p in S_bad} alpha_p Q_p,                                            (A7)
    alpha_p = [(F_mod)_p:Q_p]/[F_mod:Q],  sum_{p|p0} alpha_p = 1.                  (A8)

F_mod=Q 时 alpha_p=1；uniform bad profile 的 Q_p=-b_p/e_p log p；native q 没有 archimedean 同类项，archimedean 只进入 h_C。good finite profile 按原 normalization 相对参考为 0。Q_C 的有限和不能用来抵消 h_inf 的符号；两者相加才是 h_C。

## 3. 符号界与 product formula

### 3.1 shell 包含的充分非正界

若实际 archimedean hull 落在源 log-shell 内，即 r_v<=pi 对所有 v|infty，则由 (A3)

    h_inf(C) <= 0.                                           (A9)

此时 h_inf 不能补偿任何正的 finite deficit D_C^Sp。注意 (A9) 的前提 H_C,inf subset I_v 是源级 shell 包含，本文没有从完整 C 证明；它是有明确前提的 strict bound，不是无条件全局事实。task-149 TC-G 也明确指出 finite all-bad 公式 (14)/(15) 不覆盖 archimedean 与 infinity branch。

### 3.2 product formula 不强制正补偿

对任意 x in F^×，标准 product formula 为

    sum_{v|infty} alpha_v log|x|_v + sum_p alpha_p v_p(x) log p = 0.   (A10)

若 x 属于 archimedean hull 的径向区域，则 log r_v >= log|x|_v。乘以 alpha_v 并对 v|infty 求和，用 (A10) 得

    h_inf(C) >= - sum_p alpha_p v_p(x) log p - log pi.        (A11)

对 F=Q：

    h_inf(C) >= - sum_p v_p(x) log p - log pi.                (A12)

若 x 是有限处整元素（所有 v_p(x)>=0，例如源积分格/整数格中的全局元素），(A12) 右端 <= -log pi < 0；product formula 只给非正下界，不能推出 h_inf>0，更不能推出 h_inf>=D_C^Sp>0。若 x 是全局单位（v_p(x)=0），(A11) 给 h_inf>=-log pi，同样不提供正补偿。若 x 在坏处有分母（v_p(x)<0），(A11) 右端可能为正，但这要求该全局元素实际落入 hull，而不是仅由 product formula 形式产生。故 product formula 单独既不能证明补偿，也不能排除 r_v>pi 的正支。

### 3.3 非径向 hull

非径向 archimedean hull 的实际读数是

    h_inf(C) = sum_{v|infty} alpha_v [ h_v^ang(A_v) + h_v^rad(R_v) ],   (A13)

其中 A_v 是角向区域、R_v 是径向区间。h_v^ang 可正可负，不能丢掉角向体积后把 (A3) 当作全读出。当前没有完整 C 的实际数据；本文的数值判据只适用于径向 hull。

## 4. finite deficit 与补偿判据（条件版）

在 task-151 的记号下，uniform profile 的 finite residual 写作

    D_C^Sp := sum_{p in S_bad} alpha_p D_p^Sp log p,            (A14)
    D_p^Sp/log p = b(e+1)/12 - (b-1)/e - T_p,                  (A15)
    T_p = (1/(e m)) sum_{j=1}^m t_j.

但按 §0 的两次纠偏，D_p^Sp 依赖 TAME (T7)/(T8) 的辛像、J=m、轨道生成和 volume 增量；它们是 donor + 标准 lattice 引理 + trace 的推断后果，不是 Kondo 定理；且 TAME (11)-(14) 的目标容器步骤需要 TC-A 至 TC-H 和 TC-S。若这些没有完成，D_p^Sp 不能登记为已证实际 finite deficit，A14 只是条件量。

在这个条件下，补偿判据为

    若 finite donor 与目标容器条件成立，则
    h_C >= Q_C  <=>  h_inf(C) >= D_C^Sp.                        (A16)

对 radial F=Q（一个实地方）即

    log(r_inf/pi) >= D_C^Sp  <=>  r_inf >= pi * exp(D_C^Sp).   (A17)

b=3、e=41、单 bad p 时 D_C^Sp=408/41：

    r_inf >= pi * exp(408/41) ≈ 65903.669.                     (A18)

b=273 时 D_C^Sp=38883/41：

    r_inf >= pi * exp(38883/41).                               (A19)

这些是精确必要条件，不是实际半径。若 S_bad 有多个 p，D_C^Sp 取和，所需 r_inf 取指数和；若 h_inf<0，A16 不可能成立。

### 4.1 三个精确分支（均为条件）

1. shell 包含支：r_v<=pi 对所有 v，则 h_inf<=0，A16 不成立（当 D_C^Sp>0）；若 finite donor 与目标容器条件也成立，全局亏损至少保持 D_C^Sp-h_inf。由于 shell 包含、finite donor、TC-A 至 TC-H 均未证，这不是已证全局反例，只是条件分支。
2. 部分补偿支：0<h_inf<D_C^Sp；剩余亏损 D_C^Sp-h_inf>0，需要更多实际源贡献。
3. 完全补偿支：h_inf>=D_C^Sp；在 finite donor 与目标容器条件成立时 A16 给 h_C>=Q_C。这需要实际 archimedean 半径超过 shell 半径 pi 的 exp(D_C^Sp) 倍，是强正半径条件；当前没有构造。

## 5. 已证 / 推断 / 条件 / 未证

### 5.1 已证（源原文/冻结文件中的自然语言事实）

1. IUT III Remark1.2.2(ii)：复 archimedean log-shell I_v={|a|<=pi}；Def1.1(ii)/(vii) 与 Prop1.2(iii),(v)：angular/radial log-volume 及 log-link 相容。
2. IUT IV Prop1.5/Thm1.10(vii) 与 AbsTopIII Prop5.7(ii)/Cor5.10(ii) 的实际 archimedean log-volume/normalization 接口；本文只使用标准径向归一化 (A2)，不重证这些定理。
3. 标准 product formula (A10)；度权 alpha_v=d_v/[F:Q]、sum alpha_v=1。
4. 初等径向体积公式 (A2)，以及由 r_v<=pi 得 h_inf<=0 的推导。
5. (A11)-(A12) 的 product-formula 下界：由 log r_v>=log|x|_v 和 (A10) 直接得到；对有限处整元素右端非正。

### 5.2 推断（本文装配，不是源定理）

6. 完整 C 的 h_inf(C)=sum alpha_v log(r_v/pi)（径向 hull 情形）及 (A6)-(A8) 的全局加权分解；r_v 来自实际 hull 尚未构造。
7. F_mod=Q、一个实地方时 alpha_inf=1 和 (A5)。
8. finite residual D_C^Sp 的数值 (A14)-(A15) 及补偿判据 (A16)；其成立依赖 task-147/task-149 修正后的 donor 与目标容器条件。

### 5.3 条件

9. 若 H_C,inf subset I_v（所有 v），则 h_inf<=0，不能补偿正 finite deficit。
10. 若 finite donor 与 TC-A 至 TC-H、TC-S 成立，则补偿的充要条件是 (A16)；对 F=Q radial 即 (A17) 的实际半径条件。

### 5.4 未证

11. 完整合格 C 的实际 archimedean hull 半径 r_v 及其正性/上界；
12. shell 包含 r_v<=pi 是否对完整 C 成立（或反例）；
13. 全 infinite places 的 angular 项；本文只给径向公式；
14. 完整 C 的有限 alpha_p/bad 集/row-Theta 权重构造（task-151 已列为 gap）；
15. 纠偏后的有限 symplectic donor 的 basis alignment 和 H 的实际轨道生成；
16. TAME (11)-(14) 的目标容器条件 TC-A 至 TC-H、TC-S；F(Hull(...)) subset H_C 不能由环同构单独推出；
17. 原全局目标 h_C>=Q_C 或完整反例；本文两者都不声称。

## 6. 结论与精确剩余缺口

实际 archimedean 读出的可写部分为：对径向 hull，

    h_inf(C)=sum_{v|infty} alpha_v log(r_v/pi),  alpha_v=[F_v:R]/[F:Q],

F=Q 时为 log(r_inf/pi)。这个公式不是 0，也不是任意项；它把补偿问题精确化为实际半径问题。

在此基础上：

- 若 r_v<=pi（源 shell 包含），则 h_inf<=0，不能补偿正 finite deficit；若 finite donor 与目标容器条件成立，亏损至少保持有限处的 D_C^Sp。
- product formula 对有限处整元素只给 h_inf>=-sum alpha_p v_p(x)log p-log pi<=-log pi，不能推出正补偿；它既不能证明补偿，也不能单独排除 r_v>pi 的正支。
- 若 r_v>pi，补偿的精确必要条件是 (A17)；b=3,e=41 单 bad p 要求 r_inf>=pi exp(408/41)≈65903.669，b=273 要求 r_inf>=pi exp(38883/41)。这些是必要条件，不是已实现半径。

剩余 gap 的准确顺序：

1. 从完整 C 的实际 archimedean 输出构造 hull 半径 r_v（含非径向 angular term）；当前没有完整 C，故 r_v 未构造。
2. 判定/证明 r_v<=pi 的 shell 包含，或给出实际 r_v>pi 的正下界；这是 archimedean 能否补偿的唯一数值门槛，不能用 product formula 代替。
3. 完成 task-151 的完整 bad 集/权重；否则 D_C^Sp 只是条件量。
4. 按 task-147 纠偏重做有限辛 donor：H=Phi^{-1}(Sp)、mapping-class/Dehn twists、basis alignment、trace target；在完成前，D_C^Sp 不能作为实际 finite deficit 使用。
5. 按 task-149 完成 TC-A 至 TC-H、TC-S；特别注意 (11)-(14) 不是目标证明，F(Hull(...)) subset H_C 和 volume preservation 未证。
6. 只有在 1-5 之后，才可把 (A16) 代入完整 C 的 h_C>=Q_C；当前 target_accepted=false，无全局闭合。

## 7. 下一步（可执行、无任意假设）

1. 在 F_mod=Q 的测试对象上，按 IUT III 的 archimedean packet 构造实际 R_{C,v}/H_C,inf，直接计算径向 r_inf（或证明 shell 包含 r_inf<=pi）。
2. 保留 angular 项；若 hull 非径向，按 (A13) 分开计算，不把角向体积丢弃。
3. 用 product formula 只作为点模长约束，不作为 hull 体积正下界；对 integral/global-unit 点记录 (A11) 的精确非正界。
4. 完成 task-147/task-149 纠偏的 finite donor 与目标容器后，再算 D_C^Sp；在纠偏前只保留条件记号，不引用原 TAME §2 的辛群像直接结论，也不把 (11)-(14) 当目标证明。
5. 最后才装配 (A16)/(A17)，并报告 h_inf 的符号、所需半径和剩余亏损。

来源位置：IUT III Remark1.2.2(ii)（archimedean shell 半径 pi）、Def1.1(ii)/(vii)、Prop1.2(iii),(v)（angular/radial log-volumes）；IUT IV Prop1.5/Thm1.10(vii)（archimedean normalization/全局权重）；AbsTopIII Prop5.7(ii)/Cor5.10(ii)（实际 archimedean log-volumes）。这些源位置经 task-146/task-147/task-148/task-149/task-151 的已核记录转引；本文没有重新逐页核对全部原文。

没有 target_accepted、kernel_closed、完整 P6 或 ABC 结论。
