# S1984: K 侧 xK/cK/cF/coverMap 对象审计

日期：2026-11-01（Asia/Shanghai）
工作目录：D:\lean
范围：IUT I Definition 3.1(d),(f)（PDF p.62-63；corpus 行 3185-3215, 3280-3288）；
[EtTh] Definition 2.1（corpus 行 2423-2432）；S1972 的 C_F/C_K signature 审计；
生产 K 侧契约 SourceSignQuotientData / SourceClauseD；paper-target
S1360KCoreIdentification / S1376PaperCore / S1881D9OrbicurveSlot / S1886D9SlotTail。
状态：审计完成；未修改任何生产定义；附 Lean audit 文件 EXIT=0。

## 0. 一页结论

1. 生产契约中的 xK/cK 在对象层面确实是 K-core：
   xK = xKExtension.result，cK = cKExtension.result
   （[SourceDefinition31Quantifiers.lean](LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L606-L613)）。
   xKExtension 是 X_F 的 scalar extension，cKExtension 是 cF 的 scalar extension；
   因此 xK 是 X_F ×_F K，cK 是 cF ×_F K，不是 degree-l 覆叠对象。
2. 但同一个结构把 xK/cK 的类型字段直接写成
   sourceTypeOneLTorsion l / sourceTypeOneLTorsionPlusMinus l
   （同文件 610-611 行），这两个标签是论文 K 侧 **覆叠** X_K^-> / C_K^-> 的类型，
   不是 K-core 的类型。这是精确的**对象/标签错位**，不是数值微调问题。
3. 生产 Clause (d) 的 k_l_torsion_cover 实际等于 sign quotient
   k_quotient：k_l_torsion_cover.map = k_quotient.map
   （[SourceDefinition31Quantifiers.lean](LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1111-L1122)）。
   所以它是 K-core 上的 ±1 商 X_K -> C_K（generic degree 2），
   **不是** degree-l 的 l-tors 覆叠 X_K^-> -> X_K 或 C_K^-> -> C_K。
   方向对（core 到 core），名字和角色错。
4. paper-target 的 coverMap 是反过来的混合体：
   S1881D9OrbicurveSlot.coverMap : xK.Hom cK，其中
   cK = core.result 是 K-core，xK 却贴 (1,l-tors) 标签
   （[S1881D9D7bActual.lean](tmp/sheaf/xif/paper/S1881D9D7bActual.lean#L165-L183)）。
   它既不是 X_K^-> -> X_K（target 不是 X_K core），
   也不是 C_K^-> -> C_K（source 不是 C_K^->），
   也不是纯粹的 X_K -> C_K（source 的标签是覆叠类型）。
5. 论文 K 侧需要四个对象和相应覆叠：
   X_K^-> -> X_K，C_K^-> -> C_K，以及商图 X_K^-> -> C_K^->；
   K-core 之间还有 X_K -> C_K。当前契约只有两个对象 xK/cK 和一个 map，
   把四类角色压成一个 xK/cK/coverMap 三元组。这是本审计的核心结论。
6. 生产 SourceCuspDerivedOrbicurves 里确实有形状接近的 xArrow/cArrow
   （xArrow -> D.xK，cArrow -> D.cK，xArrow -> cArrow），
   但它们住在独立的 SourceOrbicurveObject carrier 模型里，
   不是 Iut.HyperbolicOrbicurve；且目标 D.xK/D.cK 在 ClauseD 中贴的是
   l-tors 标签，不是 core 标签
   （[SourceInitialThetaData.lean](LeanFormal/IUT/IUTI/InitialTheta/SourceInitialThetaData.lean#L2670-L2698)）。
   因此它们是**代替模型**，不能直接充当实际 stack 覆叠。
7. S1376 的修复方向需要纠正：它删除了 xKExtension/xK_eq_extension，
   并声称 X_K 不是 X_F 的 scalar extension
   （[S1376PaperKCoreRestatementActual.lean](tmp/sheaf/xif/paper/S1376PaperKCoreRestatementActual.lean#L4-L32)）。
   这与 IUT I p.3、p.63 的 X_K := X_F ×_F K 冲突；正确做法是保留 xK 为 core，
   另加 X_K^-> 覆叠，而不是把 core 换成覆叠。
8. 精确 first missing 是：实际的 Iut.HyperbolicOrbicurve 对象
   X_K^-> / C_K^->，以及它们到 cores 的 degree-l finite etale 覆叠和
   quotient square。core 对象和 core quotient 在生产里已有，可由现有数据构造
   （见本包 Lean 文件 S1984PaperKCore.ofSource）。
   标签 retype、[EtTh] 类型桥和 C_F honest quotient 是另外的、需要 lead 决策的 target 问题。

## 1. 论文对象：四个对象，不是两个

### 1.1 K-core

IUT I p.3：

    ... a finite etale covering C_K^-> -> C_K of degree l such that the
    base-changed covering X_K^-> := C_K^-> ×_{C_F} X_F -> X_K := X_F ×_F K ...
    (corpus 行 119-125)

IUT I p.63, Definition 3.1(f)：

    Thus, the data (X_K := X_F ×_F K, C_K, ε) determines hyperbolic orbicurves
    X_K^->, C_K^-> of type (1,l-tors^->), (1,l-tors^->)^±, respectively ...
    (corpus 行 3280-3288)

这里 X_K := X_F ×_F K、C_K := C_F ×_F K 是 K-core；X_K^->、C_K^-> 是
degree-l 覆叠。S1972 给出的四对象表与此一致
（[S1972CFSignatureAudit.md](coord/reports/S1972CFSignatureAudit.md#L119-L125)）。

### 1.2 记号重载

IUT I p.62 Definition 3.1(d) 还写道：

    C_K is a hyperbolic orbicurve of type (1,l-tors)^± ... with K-core ...
    given by C_K := C_F ×_F K ... In particular, C_K determines ... X_K of type
    (1,l-tors) ... together with natural cartesian diagrams
    X_K -> X_F, C_K -> C_F
    (corpus 行 3185-3197)

PDF p.62 中这些 C_K/X_K 带下划线，而同页的 K-core 又写成
C_K := C_F ×_F K。论文在这里把 K-core 与带 l-tors 装饰的对象用了同一个字母；
下划线的印刷读法不影响 Lean 侧的对象方程结论，因为 xK/cK 已由 scalar
extension 等式固定为 K-core。
本审计采用 S1972 的操作性读法：

* K-core 对象：X_K := X_F ×_F K，C_K := C_F ×_F K；
* 带 l-tors 装饰的对象/覆叠：X_K^->，C_K^->；
* 标签 typeOneLTorsion / typeOneLTorsionPlusMinus 属于后者。

这个区分不依赖下划线的排版解释：Lean 的 xK/cK 由等式
xK = xKExtension.result、cK = cKExtension.result 固定为 scalar extension 的
结果，即 K-core；标签却写成覆叠类型，错位在对象方程层面已经成立。

### 1.3 论文的 arrows

按 IUT I p.3、p.62-63 和 [EtTh] Definition 2.1：

    X_K -> X_F                 (core 到 F-core)
    C_K -> C_F                 (core 到 F-core)
    X_K -> C_K                 (±1 core quotient)
    X_K^-> -> X_K              (degree-l l-tors cover)
    C_K^-> -> C_K              (degree-l l-tors cover)
    X_K^-> -> C_K^->           (±1 quotient of covers)

当前 Lean 契约没有任何一个结构同时含这六个箭头。生产 Clause (d) 的
k_quotient 只提供 X_K -> C_K；paper-target 的 coverMap 只提供
xK -> cK 一个混合箭头；S1376 的 k_quotient_map_eq_kCore_cover 也只是把
X_K -> C_K 认成 kCore.coverMap。X_K^-> -> X_K 和 C_K^-> -> C_K 没有出现。

## 2. Lean 实际对象

### 2.1 SourceSignQuotientData

文件：[SourceDefinition31Quantifiers.lean](LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L578-L631)

字段：

    xK : HyperbolicOrbicurve A.K
    cK : HyperbolicOrbicurve A.K
    xKExtension : SourceOrbicurveScalarExtension A.F A.K xF
    cKExtension : SourceOrbicurveScalarExtension A.F A.K cF
    xKType : xK.signature = sourceTypeOneLTorsion l
    cKType : cK.signature = sourceTypeOneLTorsionPlusMinus l
    xK_eq_extension : xK = xKExtension.result
    cK_eq_extension : cK = cKExtension.result

实际对象判定：

* xK：由 xK_eq_extension，等于 X_F 的 scalar extension 结果。对象是 K-core
  X_F ×_F K；没有 degree-l cover、没有 E_K[l] ↠ Q、没有 X_K^-> 对象。
* cK：由 cK_eq_extension，等于 cF 的 scalar extension 结果。对象是 K-core
  C_F ×_F K；没有 C_K^-> 对象、没有 degree-l cover。
* cF：是 quotient 的 codomain：
  quotient : OrbicurveSignInvariantMorphism signAction cF，
  quotientWitness : OrbicurveSignQuotientWitness signAction quotient。
  所以 cF 在对象层面是 actual sign quotient 的 codomain（条件于这些字段）；
  但结构里没有 cF signature 字段。
* cF_genus：定理 cF_genus 由 cKExtension.genus_preserved 和 cKType 推出
  S.cF.signature.genus = 1
  （同文件 681-689 行）。这是被错标签反推出来的 metadata；
  S1972 的 honest C_F 是 genus 0。该定理不能被当作 cF 的几何事实。

### 2.2 SourceClauseD：k_l_torsion_cover 实际是 core quotient

文件：[SourceDefinition31Quantifiers.lean](LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1106-L1144)

字段：

    k_signAction : OrbicurveSignAction S.xK
    k_quotient : OrbicurveSignInvariantMorphism k_signAction S.cK
    k_quotientWitness : OrbicurveSignQuotientWitness k_signAction k_quotient
    k_l_torsion_cover : SourceOrbicurveFiniteEtaleCover S.xK S.cK
    k_l_torsion_cover_map_eq_quotient :
      k_l_torsion_cover.map = k_quotient.map

判定：

* k_quotient 是 sign action 的商映射，即 X_K -> C_K 的 ±1 quotient。
* k_l_torsion_cover 的 map 被证明等于 k_quotient.map；因此它不是
  degree-l 的 l-tors 覆叠，而是同一个 core quotient 换了名字。
* 名字 "l_torsion_cover" 与对象的数学角色不符；这不是 degree-l cover 的
  数据缺失，而是把已有 core quotient 错误地记成了 l-tors cover。

### 2.3 SourceInitialThetaData.ClauseD / SourceCuspDerivedOrbicurves

文件：[SourceInitialThetaData.lean](LeanFormal/IUT/IUTI/InitialTheta/SourceInitialThetaData.lean#L1856-L1896) 和
[SourceInitialThetaData.lean](LeanFormal/IUT/IUTI/InitialTheta/SourceInitialThetaData.lean#L2670-L2698)

ClauseD 的字段：

    xF_type : D.xF.signature = typeOneOne
    cF_type : D.cF.signature = typeOneOne
    xK_type : D.xK.signature = typeOneLTorsion l
    cK_type : D.cK.signature = typeOneLTorsionPlusMinus l
    xK_to_xF : SourceOrbicurveCrossFieldMorphism D.xK D.xF
    cK_to_cF : SourceOrbicurveCrossFieldMorphism D.cK D.cF
    xK_cK_cover : SourceOrbicurveMorphism D.xK D.cK

SourceCuspDerivedOrbicurves 的字段：

    xArrow : SourceOrbicurveObject K
    cArrow : SourceOrbicurveObject K
    xArrow_signature : xArrow.signature = typeOneLTorsion l
    cArrow_signature : cArrow.signature = typeOneLTorsionPlusMinus l
    xArrow_to_xK : SourceOrbicurveMorphism xArrow D.xK
    cArrow_to_cK : SourceOrbicurveMorphism cArrow D.cK
    xArrow_to_cArrow : SourceOrbicurveMorphism xArrow cArrow

判定：

* 这个 contract 里的 D.xK/D.cK 按 ClauseD 的标签是 (1,l-tors)/(1,l-tors)^±
  对象，不是 K-core；ClauseD 没有 xK = xKExtension.result 之类的 core 方程。
* xArrow -> D.xK 和 cArrow -> D.cK 的方向形状像论文，但目标对象是覆叠标签的
  xK/cK，不是 core。因此是 cover -> cover，不是 cover -> core。
* SourceOrbicurveObject 是独立的 carrier 模型
  （[SourceInitialThetaData.lean](LeanFormal/IUT/IUTI/InitialTheta/SourceInitialThetaData.lean#L108-L115)）：
  carrier : Type，signature : SourceOrbicurveSignature，finite_etale : Prop；
  SourceOrbicurveMorphism 的 map 是 carrier -> carrier 的函数
  （[SourceInitialThetaData.lean](LeanFormal/IUT/IUTI/InitialTheta/SourceInitialThetaData.lean#L1778-L1801)），
  不是 Iut.HyperbolicOrbicurve.Hom。本审计未发现该模型到实际 etale stack
  的 bridge；现有类型上不能直接 coercion。
* 因此这里即使有 X_K^->/C_K^-> 的形状，也不是实际的
  Iut.HyperbolicOrbicurve 对象；不能填入生产 K-side stack 契约。

### 2.4 S1360 / S1376：把 core 删掉、把覆叠当 core

S1360KCoreBaseChange / S1360KCoreIdentification
（[S1360D9OrbicurveSlotActual.lean](tmp/sheaf/xif/paper/S1360D9OrbicurveSlotActual.lean#L199-L224)）：

    cF : HyperbolicOrbicurve F
    cK : HyperbolicOrbicurve K
    cKExtension : SourceOrbicurveScalarExtension F K cF
    cK_eq_extension : cK = cKExtension.result
    cK_type : cK.signature = typeOneLTorsionPlusMinus l
    x_type : X.signature = typeOneLTorsion l
    coverMap : X.Hom cK
    coverFiniteEtale : EtaleStackFiniteEtaleMorphism coverMap

这里 X 被声明为 (1,l-tors) 对象；coverMap 的目标 cK 是 scalar extension 结果
（core C_F × K），但 cK_type 又贴 (1,l-tors)^±。所以 coverMap 是
"l-tors 标签的对象 -> core 标签的对象"，不是 X_K^-> -> X_K。

S1376 进一步把 xK 的 core 方程整个删掉：

    The restated core contains no xKExtension/xK_eq_extension field ...
    X_K is *not* the scalar extension X_F x_F K; the l-torsion decoration of
    X_K is additional K-side structure.
    ([S1376PaperKCoreRestatementActual.lean](tmp/sheaf/xif/paper/S1376PaperKCoreRestatementActual.lean#L4-L32))

这与 IUT I p.3/p.63 的 X_K := X_F ×_F K 相冲突。S1376 的 ofGeometricCore
甚至直接把旧 core 的 G.xK（= xKExtension.result）当作 l-tors 的 X_K，
并令 coverMap := cover.map
（[S1376PaperKCoreRestatementActual.lean](tmp/sheaf/xif/paper/S1376PaperKCoreRestatementActual.lean#L298-L325)）。
这把对象错位固化了，而不是修复它。

### 2.5 S1881 / S1886：hybrid coverMap

S1881D9OrbicurveSlot
（[S1881D9D7bActual.lean](tmp/sheaf/xif/paper/S1881D9D7bActual.lean#L165-L183)）：

    cF : HyperbolicOrbicurve F
    cF_signature : cF.signature = sourceTypeOneOnePlusMinus
    core : SourceOrbicurveScalarExtension F K cF
    cK : HyperbolicOrbicurve K
    cK_eq : cK = core.result
    cK_signature : cK.signature = sourceTypeOneLTorsionPlusMinus l
    xK : HyperbolicOrbicurve K
    xK_signature : xK.signature = sourceTypeOneLTorsion l
    coverMap : xK.Hom cK
    coverFiniteEtale : EtaleStackFiniteEtaleMorphism coverMap

实际对象：

* cK = core.result：对象是 C_F 的 K-core。
* xK：对象没有 scalar extension 或 core 方程；只有 (1,l-tors) 标签。
* coverMap 的目标 cK 是 core，source xK 是覆叠标签。论文没有
  "decorated X_K -> K-core C_K" 这个 arrow；因此 coverMap 是 hybrid。

S1886 把 slot 分解成 S1886KCore + S1886XKCoverData
（[S1886D9OrbicurveActual.lean](tmp/sheaf/xif/paper/S1886D9OrbicurveActual.lean#L98-L112)，
[S1886D9OrbicurveActual.lean](tmp/sheaf/xif/paper/S1886D9OrbicurveActual.lean#L162-L176)）。
S1886KCore.signature 仍是 core.result.signature = typeOneLTorsionPlusMinus；
S1886XKCoverData 的 cover 是 xK -> K.core.result，而不是 xK -> X_K core。
S1886D9SlotTail_nonempty_iff 只是把这个错位分解成两个字段，不修复对象。

## 3. 精确对象错位

### 3.1 xK

| 项目 | 内容 |
|---|---|
| Lean 对象 | xK = xKExtension.result（SourceSignQuotientData 606-613） |
| 论文对象 | K-core X_K := X_F ×_F K（IUT I p.3, p.63） |
| 标签 | sourceTypeOneLTorsion l（(1,l-tors) cover 类型） |
| 判定 | 对象对，标签错；实际 X_K^-> 缺失 |

### 3.2 cK

| 项目 | 内容 |
|---|---|
| Lean 对象 | cK = cKExtension.result（SourceSignQuotientData 606-613） |
| 论文对象 | K-core C_K := C_F ×_F K（IUT I p.3, p.63） |
| 标签 | sourceTypeOneLTorsionPlusMinus l（(1,l-tors)^± cover 类型） |
| 判定 | 对象对，标签错；实际 C_K^-> 缺失 |

### 3.3 cF

| 项目 | 内容 |
|---|---|
| 生产对象 | quotient 的 codomain：OrbicurveSignInvariantMorphism signAction cF + witness |
| 生产标签 | 没有 cF signature 字段；cF_genus 由错标签反推出 genus = 1 |
| paper-target | S1881CF 只是带 label 的 subtype；S1360KCoreBaseChange.cF 没有 quotient 字段 |
| 判定 | 生产对象层面是 actual quotient codomain；metadata 被 cK 标签污染。S1881 的 cF 不是 honest C_F，first missing 仍是 C_F quotient（S1972 M1 / S1886PaperCF） |

### 3.4 coverMap / k_l_torsion_cover

| 契约 | 实际类型/等式 | 实际角色 | 论文角色 |
|---|---|---|---|
| SourceClauseD.k_l_torsion_cover | SourceOrbicurveFiniteEtaleCover S.xK S.cK，map = k_quotient.map | X_K -> C_K core ±1 quotient | 不是 l-tors cover；论文这是 X_K -> C_K |
| S1881.coverMap | xK.Hom cK，cK = core.result | decorated X_K -> K-core C_K | 论文没有这个 arrow；X_K^-> -> X_K 或 C_K^-> -> C_K 的 target 都不是这个 cK 标签 |
| S1360.coverMap | X.Hom cK，X 贴 l-tors | 同上 | 同上 |
| SourceCuspDerivedOrbicurves.xArrow_to_xK | xArrow -> D.xK，D.xK 贴 l-tors | cover -> cover | 方向对，目标对象错（应是 core X_K） |
| SourceCuspDerivedOrbicurves.cArrow_to_cK | cArrow -> D.cK，D.cK 贴 l-tors± | cover -> cover | 方向对，目标对象错（应是 core C_K） |
| SourceCuspDerivedOrbicurves.xArrow_to_cArrow | xArrow -> cArrow | X_K^-> -> C_K^->（形状最接近） | 形状最接近论文的 arrow，但对象在代替模型里，且标签数值错 |

### 3.5 四重角色坍缩

一个 xK/cK 对和一个 map 被要求同时承担：

1. xK 作为 core X_K（生产对象方程）；
2. xK 作为 cover X_K^->（生产标签 / S1881 标签）；
3. cK 作为 core C_K（生产对象方程 / S1881 cK_eq）；
4. cK 作为 cover C_K^->（生产标签 / S1881 标签）；
5. coverMap/k_l_torsion_cover 作为 core quotient X_K -> C_K；
6. 同时作为 X_K^-> -> X_K；
7. 同时作为 C_K^-> -> C_K；
8. 同时作为 X_K^-> -> C_K^->。

这 8 个角色不能由 2 个对象和 1 个 arrow 同时满足。论文的四个对象
X_K, C_K, X_K^->, C_K^-> 和这些 arrows 必须拆开。

## 4. 不矛盾，但不是 paper-faithful

* signature 是自由 metadata：EtaleStackOverField.orbicurveSignature : Option
  OrbicurveSignature，HyperbolicOrbicurve.signature 只是 geometry.signature；
  没有定理把标签与 fiber 的几何强制联系起来。
* 因此本审计的标签错位不会产生 Lean 逻辑矛盾；本包 Lean 文件证明的是
  **角色不相容**（label inequality + no-go），不是几何不存在。
* 反过来，不能从 Lean 的 xK.signature/cK.signature 读出 xK/cK 的真实几何。
  cF_genus = 1 只是字段后果，不是 C_F 的几何事实。

## 5. 修正建议（不修改生产定义）

### 5.1 最小一致性修复（不改 target）

1. 把 SourceClauseD.k_l_torsion_cover 重命名为 k_core_quotient（连同
   k_l_torsion_cover_map_eq_quotient 改为 k_core_quotient_map_eq_quotient）。
   它的 map 已经等于 k_quotient.map，这是 core quotient，不是 l-tors cover。
2. 在 SourceClauseD 的 docstring 明确：k_quotient 是 X_K -> C_K 的 ±1 商；
   l-tors 覆叠不在本结构里。
3. 保留 xK/cK 的 core 方程；不要把 xK/cK 改名成 X_K^->/C_K^->，也不要把
   xK_eq_extension/cK_eq_extension 删除。
4. S1360/S1376/S1881/S1886 中把 coverMap 改名为 coreQuotient（如果 source
   确实按 core 读），或保留 coverMap 但明确 target 是 C_K core，不是
   X_K^->/C_K^-> 的箭头。

### 5.2 Paper-faithful K-side 拆分（需要 target 决策）

建议新增一个 K-side cover record（名字示例 SourceKCoreCovers），字段：

    xArrow : HyperbolicOrbicurve K
    cArrow : HyperbolicOrbicurve K
    xArrow_type : xArrow.signature = sourceTypeOneLTorsion l
    cArrow_type : cArrow.signature = sourceTypeOneLTorsionPlusMinus l
    xArrow_to_xK : xArrow.Hom xK
    cArrow_to_cK : cArrow.Hom cK
    xArrow_to_cArrow : xArrow.Hom cArrow
    finite etale certificates

其中 xK/cK 仍用 SourceSignQuotientData 的 core（xK = xKExtension.result,
cK = cKExtension.result）；xArrow_to_xK 是 X_K^-> -> X_K，cArrow_to_cK 是
C_K^-> -> C_K，xArrow_to_cArrow 是 X_K^-> -> C_K^->。core quotient
X_K -> C_K 继续用 k_quotient。这样四个对象和 arrows 都拆开。

关键：优先复用现有 SourceCuspDerivedOrbicurves 的 arrow 形状，但必须：

* 把 SourceOrbicurveObject 的 carrier/signature 模型桥接到实际
  Iut.HyperbolicOrbicurve；当前没有这个 bridge；
* 把 D.xK/D.cK 的 target 从 l-tors 标签改为 core 标签，或另加 core 字段；
* 接上 ClauseC 的 rank-one quotient / E_K[l] ↠ Q 数据，给出 degree-l 证书。

### 5.3 paper-target 修正

S1881/S1886：

* 增加核心 X_K 字段（scalar extension of xF），不要把 xK 同时当 core 和 cover。
* cK 保持 core.result 的对象方程；把 cK_signature 改为 core 标签。
* 增加 cArrow : C_K^-> 和 cArrow -> cK；coverMap 改成 xK^-> -> X_K core，
  不再以 cK 为 target。
* S1886XKCoverData.cover 的 target 从 K.core.result 改为 X_K core；
  S1886D9SlotTail 的 fields 随之拆分。

S1360/S1376：

* 恢复 xKExtension/xK_eq_extension（IUT I p.3/p.63 明确 X_K := X_F ×_F K）。
* S1360KCoreIdentification 的 coverMap 改为 X_K -> C_K core quotient；
  l-tors cover 另立字段，target 是 xK core。
* S1376PaperCore 不要删除 xK 的 scalar extension；把 X_K^-> 作为新字段，
  而不是把 X_K 说成不是 scalar extension。

### 5.4 标签

* xK/cK 的 core 标签应回到 (1,1)/(1,1)^±；honest 数值按 S1972 为
  (1;[];1)/(0;[2,2,2];1)。
* xArrow/cArrow 的标签应为 (1,l-tors)/(1,l-tors)^±；honest 数值按 S1972 为
  (1;[];l)/(0;[2,2,2];(l+1)/2)。
* 改 sourceTypeOneOnePlusMinus / sourceTypeOneLTorsion /
  sourceTypeOneLTorsionPlusMinus 的数值会改变所有下游 target 的 elaborated
  type，属于 target 锁定层面决定；本审计不擅自改。

明确不做：

* 不只把 sourceTypeOneLTorsion 的数字改成 (1;[];l) 而保留 xK 为 core；
* 不把 cKType 改名成 cFType 来掩盖 cF genus 0 的缺失；
* 不把 SourceCuspDerivedOrbicurves 的代替模型直接当作实际 stack；
* 不把 S1881CF 当作 honest C_F；它仍缺 sign action/quotient/witness。

## 6. 正确对象 / 精确 first missing

### 6.1 已可构造的 core half

本包 Lean 文件定义并构造了 S1984PaperKCore：

    xK := S.xK
    cK := S.cK
    xKExtension := S.xKExtension
    cKExtension := S.cKExtension
    xK_eq := S.xK_eq_extension
    cK_eq := S.cK_eq_extension
    coreQuotient := E.k_quotient.map
    coreQuotient_finiteEtale := ...（由 k_l_torsion_cover.finiteEtale 运输）

定理 S1984PaperKCore.ofSource_coreQuotient_eq_lTorsionCover 证明这个
coreQuotient 正是生产里名为 k_l_torsion_cover 的 map。也就是说：
生产数据已经给出 paper K-core 的 xK, cK, X_K -> C_K；不需要新增对象。

### 6.2 精确 first missing

定义 S1984PaperKCoverData（本包 Lean 文件第 7 节）为：

    xArrow, cArrow : Iut.HyperbolicOrbicurve A.K
    xArrow_type : xArrow.signature = sourceTypeOneLTorsion l
    cArrow_type : cArrow.signature = sourceTypeOneLTorsionPlusMinus l
    xArrow_to_xK : xArrow.Hom C.xK
    cArrow_to_cK : cArrow.Hom C.cK
    xArrow_to_cArrow : xArrow.Hom cArrow
    finite etale certificates

S1984PaperKCoverMissing C := Nonempty (S1984PaperKCoverData ... C)。

这不是一个数字错误；它是：

1. **实际 stack 对象**：X_K^->、C_K^-> 必须是 Iut.HyperbolicOrbicurve；
   目前生产只有 SourceOrbicurveObject 代替模型，paper-target 只有未构造的
   slot fields。
2. **degree-l finite etale 覆叠**：xArrow -> xK、cArrow -> cK；当前
   EtaleStackFiniteEtaleMorphism 只记录 finite etale，没有 degree-l 字段；
   degree-l 需要接 rank-one quotient / [EtTh] 构造。
3. **quotient square**：xArrow -> cArrow 与 xArrow -> xK、cArrow -> cK 的
   compatibility；以及 xArrow -> cArrow -> cK 与 xArrow -> xK -> cK 的
   2-isomorphism。
4. **标签桥**：把上述对象接到正确的 type 标签；这需要 [EtTh] 类型名到
   OrbicurveSignature 的桥（S1972 M2），不是 axiom 能代替的。
5. **F 侧 C_F quotient**：若走 S1881/S1886 paper-target，cF 仍需 actual
   sign action/quotient/witness；生产 SourceSignQuotientData 把它作为字段，
   S1881CF 则不是 honest quotient。

### 6.3 各契约的 first missing

| 契约 | 已有 | 精确 first missing |
|---|---|---|
| SourceSignQuotientData | xK/cK core + scalar extensions + sign quotient codomain | xArrow/cArrow 对象；core 标签 |
| SourceClauseD | X_K -> C_K core quotient | 真正的 l-tors covers；不要再把 core quotient 叫 l-tors cover |
| SourceInitialThetaData.ClauseD / SourceCuspDerivedOrbicurves | 代替模型里的 xArrow/cArrow 形状与 labels | 到实际 Iut.HyperbolicOrbicurve 的 bridge；core targets；rank-one quotient 连接 |
| S1360KCoreIdentification | cK core + 一个 l-tors X + cover X -> cK | core X_K；把 cover 改为 X -> X_K；cArrow |
| S1376PaperCore | 删除了 xKExtension，只有 xK + kCore | 恢复 X_K = X_F × K core；另立 X_K^-> cover |
| S1881D9OrbicurveSlot | cF label + cK core + xK label + coverMap | core X_K；coverMap 改 target；cArrow；cF actual quotient |
| S1886D9SlotTail | 上述的分解 | 同上；XKCoverData.cover 的 target 改为 X_K core |

## 7. Lean 证据

文件：tmp/sheaf/s1984/S1984KSideObjectAudit.lean
（445 行，18404 bytes，SHA256 7700AAD9A3207FDBFD00F82675B6DDFBB7A01CBD2947A956217F8EBF356AB2A4）

编译：

    lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/s1984/S1984KSideObjectAudit.olean tmp/sheaf/s1984/S1984KSideObjectAudit.lean

结果：EXIT = 0；无 error、无 warning、无 sorry/admit/axiom。
olean：.lake/build/lib/lean/tmp/sheaf/s1984/S1984KSideObjectAudit.olean
（603352 bytes，SHA256 ACF2A3E0ED47467791F43A5CCD06349E0F7F62CC7A5E095B7EA7668B59B3E973）。
Axiom probe（tmp/sheaf/s1984/S1984AxiomProbe.lean）EXIT = 0；
所列 14 条 declaration 的 #print axioms 只含 propext, Classical.choice,
Quot.sound。

关键声明：

* sourceTypeOneOne_ne_sourceTypeOneLTorsion
* sourceTypeOneOnePlusMinus_ne_sourceTypeOneLTorsionPlusMinus
* sourceSignQuotient_xK_is_core / sourceSignQuotient_cK_is_core
* sourceSignQuotient_xK_label / sourceSignQuotient_cK_label
* sourceSignQuotient_xK_not_core_label / sourceSignQuotient_cK_not_core_label
* sourceSignQuotient_cK_not_XK_core_label
* sourceSignQuotient_cF_is_quotient_codomain
* sourceSignQuotient_cF_genus_one
* sourceClauseD_lTorsionCover_eq_quotient
* sourceClauseD_lTorsionCover_target_is_cK
* sourceClauseD_lTorsionCover_not_paper_XK_cover
* sourceClauseD_lTorsionCover_not_paper_CK_cover
* s1881_cK_is_core / s1881_cK_label / s1881_xK_label / s1881_coverMap_type
* s1881_cK_not_XK_core / s1881_xK_not_XK_core / s1881_cK_not_CK_core
* s1881_no_paper_XK_cover_target / s1881_no_paper_CK_cover_target
* s1360_coverMap_target_not_XK_core / s1360_coverMap_target_not_CK_core
* S1984PaperKCore.ofSource
* S1984PaperKCore.ofSource_coreQuotient_eq_lTorsionCover
* S1984PaperKCoverData / S1984PaperKCoverMissing
* S1984PaperKChain / S1984PaperKChain_nonempty_iff
* S1984ActualOrbicurveLift / S1984DerivedLiftMissing

验收状态：

    statement_compiles: yes（EXIT 0）
    proof_body_checked: yes（无 sorry；所有声明已证）
    kernel_closed: yes（对 audit 文件的 #print axioms 而言，仅 trio）
    target_accepted: not applicable / no（本文件是审计，不是锁定 target；
                      l-tors 对象和标签桥仍缺，见第 6 节）

## 8. 未改定义声明与下一步

* 未编辑任何生产 Lean 文件；未改 SourceDefinition31Quantifiers.lean、
  SourceInitialThetaData.lean、S1360/S1376/S1881/S1886。
* 本审计新增 tmp/sheaf/s1984/S1984KSideObjectAudit.lean、
  tmp/sheaf/s1984/S1984AxiomProbe.lean 和本报告。
* 工作树中已有的 modified 文件不是本审计的改动。
* 下一步（按优先级）：
  1. 由 lead 决定是否做 paper-faithful K-side 拆分（5.2）。若不拆分，至少
     先把 k_l_torsion_cover 改名为 core quotient，避免继续把 core quotient
     当 l-tors cover 使用。
  2. 若拆分，先做实际 Iut.HyperbolicOrbicurve 的 X_K^->/C_K^-> 对象与
     degree-l 覆叠，再接 ClauseC 的 rank-one quotient；不要先改标签数值。
  3. 标签 retype 与 [EtTh] 类型桥单独作为 target 决策；它会影响 S1881/S1886、
     S1964 和所有 D-clause 消费者。
  4. 修正 S1376 的“X_K 不是 scalar extension”叙述；论文 X_K := X_F ×_F K，
     l-tors 覆叠是另加的对象。
