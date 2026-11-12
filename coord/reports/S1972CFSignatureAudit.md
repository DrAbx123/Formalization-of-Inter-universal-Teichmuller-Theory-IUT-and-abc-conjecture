# S1972: C_F / C_K 的 signature 标签、puncture 与 2-torsion 约定审计

日期：2026-11-01（Asia/Shanghai）
工作目录：D:\lean
范围：IUT I Definition 3.1；[EtTh] Section 0, Definition 2.1, 2.3；[AbsAnab II] Section 0；
LeanFormal/IUT/IUTI/InitialTheta 的 signature 标签；S1964 的 actual S1726 模型结论。
状态：审计完成；未改任何生产定义；附 Lean audit 文件 EXIT=0。

## 0. 一页结论

1. 论文的 (1,1)^± **不是**一个数值 signature。它是 [EtTh] Section 0 定义的
   "把 type (1,1) 曲线对 ±1 取 stack 商所得的 stable log orbicurve" 的类型名；
   [AbsAnab II] Section 0 的 semi-elliptic 定义给出同一意思。IUT I Def 3.1(b)
   对 C_F 只说 "stack-theoretic quotient of X_F by -1"，没有给出
   (g; stacky orders; punctures) 数值。
2. 由论文数据（X_F 是 once-punctured elliptic curve；2-torsion 在 F 上有理；
   origin 被挖掉）唯一算出：C_F = [X_F/{±1}] 的 honest signature 是
   (0; [2,2,2]; 1)，orbifold Euler characteristic = -1/2，hyperbolic。
   这正是 S1964 在实际 S1726 模型上证明的结论。
   C_K := C_F ×_F K（K-core）同样是 (0; [2,2,2]; 1)。
   K 侧的 type (1,l-tors) / (1,l-tors)^± 对象（degree-l 覆叠 X_K^->, C_K^->）
   的 honest signature 分别是 (1; []; l) 和 (0; [2,2,2]; (l+1)/2)，
   Euler characteristic 分别为 -l 和 -l/2。
3. Lean 的 sourceTypeOneOnePlusMinus = (1; [2]; 0)
   （SourceDefinition31Quantifiers.lean:295）是**转写错误**：它把 ^± 读成
   "加一个 2 阶 stacky 点"，同时把 covering curve 的 genus 1 当作商空间的
   genus，并丢掉 puncture。三个字段全错：genus 1 vs 0，stacky orders [2] vs
   [2,2,2]，punctures 0 vs 1。只有 Euler characteristic 巧合相同（都是 -1/2），
   所以只检查 hyperbolicity / χ 的测试无法发现该错误。
4. 生产 D-clause 的 C_F 标签是 sourceTypeOneOne = (1; []; 1)
   （SourceInitialThetaData.lean:1859, 3331; SourceDefinition31D5D8Root.lean:283-285;
   Definition31D0D11Aligned.lean:743-745）。那是 X_F 的 signature，不是商的；
   其 χ = -1，与论文强制的 -1/2 不同。SourceSignQuotientData 没有 cF signature
   字段，却由 cK 标签和 genus preservation 推出 cF_genus = 1
   （SourceDefinition31Quantifiers.lean:681-689），与论文强制的 genus 0 冲突。
5. K 侧是**对象错位**（object misplacement），并叠加同样的转写错误：
   SourceSignQuotientData 里只有 K-core xK = xF × K、cK = cF × K
   （xK_eq_extension, cK_eq_extension），而 sourceTypeOneLTorsion /
   sourceTypeOneLTorsionPlusMinus 是论文 degree-l 覆叠 X_K^-> / C_K^-> 的类型名。
   契约把 l-tors 类型贴到了 core 上，并且没有 X_K^-> / C_K^-> 这两个对象。
   即使把它们当作 type (1,l-tors) 对象的 signature，(1; [l]; 0) /
   (1; [2,l]; 0) 也是错的（应为 (1; []; l) / (0; [2,2,2]; (l+1)/2)）。
6. 没有 Lean 逻辑矛盾：Iut.HyperbolicOrbicurve.signature 是自由 metadata
   （EtaleStackOverField.orbicurveSignature : Option OrbicurveSignature 是字段；
   realizedHyperbolicOrbicurve 把它按构造插入），S1964 也证明了 same fiber
   可以带不同 signature（S1964SignatureLabelsNotDeterminedByFiber）。所以
   不能靠"改定义"消除，也不能把 cF_genus = 1 当作几何事实。
7. 精确 missing 不是标签本身，而是：
   (M1) 商 stack [X_F/{±1}] 的构造（S1964FirstMissing = Nonempty
        (S1964QuotientStructure l A)），其第一 missing field 是
        category-valued etale stack 的构造 / stackification / 双范畴普遍性；
   (M2) 从 [EtTh] 类型名到 OrbicurveSignature 的形式化桥（把
        (1,1)^±, (1,l-tors), (1,l-tors)^± 与其 honest signature 联系起来）；
   (M3) K 侧的 X_K^-> / C_K^-> 对象（当前契约只有 core）；
   (M4) 对现有标签/target 的处置决定（需要 lead/user 决定是否改 target 定义，
        不属于本审计擅改范围）。
   改 sourceTypeOneOnePlusMinus 为 (0; [2,2,2]; 1) 只会改变 target 的
   elaborated type，既不构造商，也不能单独解决 paper-faithfulness。

## 1. 原文锚点

以下引用使用仓库内的文本抽取；关键短语与 PDF 一致：
papers/motizuki_corpus/text/Inter-universal Teichmuller Theory I.txt（IUT I, May 2020），
papers/motizuki_corpus/text/The Etale Theta Function and its Frobenioid-theoretic
Manifestations.txt（EtTh, December 2008），
papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry II.txt
（AbsAnab II, October 2013）。PDF 原件在 papers/motizuki_corpus/raw/。

### 1.1 IUT I, Definition 3.1(b)

IUT I, Def 3.1(b)（文本行 3131-3137）：

    XF is a once-punctured elliptic curve [i.e., a hyperbolic curve of type
    (1,1)] over F ... Write EF for the elliptic curve over F determined by XF
    [so XF ⊆ EF]; XF → CF for the hyperbolic orbicurve [cf. §0] over F
    obtained by forming the stack-theoretic quotient of XF by the unique
    F-involution [i.e., automorphism of order two] "-1" of XF

同一定义的 (b) 末尾（文本行 3171-3175）还假设：

    the field extension F/Fmod is Galois of degree prime to l, and that the
    2·3-torsion points of EF are rational over F.

关键点：C_F 是 stack quotient，不是 coarse quotient；2-torsion 的 F-有理性
保证三个非零 2-torsion 点是 F-rational 的 stacky 点。论文在这里**没有**给出
任何 (g; stacky; punctures) 数值。

### 1.2 IUT I, Definition 3.1(d),(f)

IUT I, Def 3.1(d)（文本行 3185-3192）：

    CK is a hyperbolic orbicurve of type (1,l-tors)± [cf. [EtTh], Definition
    2.1] over K, with K-core [cf. [CanLift], Remark 2.1.1; [EtTh], the
    discussion at the beginning of §2] given by CK := CF ×F K. ... In
    particular, CK determines, up to K-isomorphism, a hyperbolic orbicurve XK
    of type (1,l-tors) [cf. [EtTh], Definition 2.1] over K, together with
    natural cartesian diagrams

        XK → XF
        ↓     ↓
        CK → CF

带装饰的原始记号在文本抽取中丢失；IUT I 引言（文本行 87-97, 119-125）
把对象关系说清楚了：

    ... XF ⊆ EF for the once-punctured elliptic curve obtained by removing
    the origin from EF, and XF → CF for the hyperbolic orbicurve obtained by
    forming the stack-theoretic quotient of XF by the natural action of {±1}.
    ... CK := CF ×F K is assumed to be a K-core ...
    This data determines ... a finite étale covering CK→ → CK of degree l
    such that the base-changed covering XK→ := CK→ ×CK XK → XK := XF ×F K
    arises from a rank one quotient EK[l] ↠ Q (≅ Z/lZ) ...

IUT I, Def 3.1(f)（文本行 3280-3285）再次说：

    the data (XK := XF ×F K, CK, ε) determines hyperbolic orbicurves
    XK→, CK→ of type (1,l-tors→), (1,l-tors→)±, respectively.

所以论文的 K 侧有四个对象，而不是两个：

    XK = XF ×F K          (core, type (1,1))
    CK = CF ×F K          (core, type (1,1)^±)
    XK→ → XK              (degree-l finite etale, type (1,l-tors))
    CK→ → CK              (degree-l finite etale, type (1,l-tors)^±)

### 1.3 [EtTh] Section 0: (1,1)^± 的定义

[EtTh], Section 0, "Curves"（文本行 340-368）：

    A morphism of log stacks Clog → Slog for which there exists an etale
    surjection S1 → S ... such that Clog1 := Clog ×S S1 may be obtained as
    the result of forming the quotient [in the sense of log stacks!] of a
    stable ... log curve Clog2 → Slog1 ... by the action of a finite group of
    automorphisms ... will be referred to as a stable log orbicurve ...
    Here, if Clog2 → Slog1 is of type (1,1), and the finite group of
    automorphisms is given by the action of "±1" [i.e., relative to the group
    structure of the underlying elliptic curve of Clog2 → Slog1], then the
    resulting stable log orbicurve will be referred to as being of type
    (1,1)±.

这是决定性的：^(±) 是 "对 ±1 取商" 的构造类型；括号里的 (1,1) 是**被商的
曲线**的类型，不是商空间的 signature。

### 1.4 [EtTh] Definition 2.1, 2.3

[EtTh], Def 2.1（文本行 2423-2432）：

    We shall refer to a smooth log orbicurve over K that arises, up to
    isomorphism, as the smooth log orbicurve Xlog→ (respectively, Clog→)
    constructed above for some choice of ΠellX ↠ Q as being of type
    (1,l-tors) (respectively, (1,l-tors)±).

构造（文本行 2332-2375）：Xlog 是 type (1,1)；ΠellX ↠ Q 给出 degree-l
covering Xlog→ → Xlog；Clog→ := Xlog→/{ι'}，其中 ι' 是 "multiplication by -1"
的 lift。也就是说，^(±) 永远表示对 elliptic involution 取 stack 商，而不是
"加一个 2 阶 stacky 点"。

[EtTh], Def 2.3（文本行 2635-2640）用同样的商构造定义 (1,l-torsΘ) /
(1,l-torsΘ)^±；与本审计的 C_F/C_K 结论无关，但同样说明 ^(±) 是构造类型。

### 1.5 [AbsAnab II] Section 0: semi-elliptic

[AbsAnab II], Section 0（文本行 198-202）：

    We shall refer to a hyperbolic orbicurve X as semi-elliptic [i.e., "of
    type (1,1)±" in the terminology of [Mzk12], §0] if there exists a finite
    etale double covering Y → X, where Y is a once-punctured elliptic curve,
    and the covering is given by the stack-theoretic quotient of Y by the
    "action of ±1" ...

这再次确认：type (1,1)^± 的对象 X 有一个 once-punctured elliptic curve Y
作为 finite etale double cover；Y → X 就是 ±1-商映射。

### 1.6 结论：不是 signature

三条独立文献一致：^(±) 是 quotient construction 的类型名。
因此：

* 不能把 (1,1)^± 直接读成 (g; stacky; punctures) = (1; [2]; 0)；
* 不能把 (1,l-tors) 读成 "genus 1 + 一个 order-l stacky point + 0 punctures"；
* 不能把 (1,l-tors)^± 读成 "(1; [2,l]; 0)"。

## 2. 由论文数据算出的 honest signature

### 2.1 C_F

命题 1. 设 X_F = E_F \ {O} 是 once-punctured elliptic curve，
C_F := [X_F/{±1}] 是 stack-theoretic quotient。假设 2-torsion 在 F 上有理
（IUT I Def 3.1(b) 的假设）。则 C_F 的 orbifold signature 是
(0; [2,2,2]; 1)，Euler characteristic -1/2。

证明.
(i) E_F/{±1} ≅ P^1；quotient map E_F → P^1 的 branch points 恰是 [-1] 的
固定点：origin O 和三个非零 2-torsion 点，ramification index 都是 2。
(ii) 三个非零 2-torsion 点在 X_F 中（它们不是 O），所以它们的像在 C_F 中是
三个 order-2 stacky points；O 被从 X_F 挖掉，所以它的像是 C_F 的唯一 puncture。
(iii) 因此 coarse space 是 P^1 减一点，genus 0；stacky orders [2,2,2]；
punctures 1。
(iv) χ = 2 - 2·0 - 1 - 3·(1 - 1/2) = -1/2。
另一条独立检验：X_F → C_F 是 degree-2 {±1}-torsor，故
χ(C_F) = χ(X_F)/2 = (2 - 2·1 - 1)/2 = -1/2。QED.

注意 puncture 约定：若把 O 也算进 quotient（即先取 compact E_F 再商），会得到
(0; [2,2,2,2]; 0)，χ = 0，**不 hyperbolic**。论文把 origin 挖掉，正是为了得到
χ = -1/2 的 hyperbolic orbicurve；S1964 的
S1964CoarseQuotientSignature_not_hyperbolic 也从另一面说明 coarse quotient
(0; []; 1) 的 χ = 1、不 hyperbolic，所以 C_F 必须是真 stacky quotient。

### 2.2 C_K (core)

C_K := C_F ×_F K 是 finite separable base change。base change 不改变 coarse
genus、stacky orders、punctures，故 C_K 的 signature 仍是 (0; [2,2,2]; 1)，
χ = -1/2。这与 IUT I 说 C_K 是 C_F 的 K-core 一致。

### 2.3 X_K^-> 与 C_K^-> (degree-l covers)

命题 2. 设 X_K^-> → X_K 是由 rank-one quotient E_K[l] ↠ Q 给出的
degree-l finite etale cyclic cover（IUT I 引言 119-125；[EtTh] Def 2.1）。
则：

    X_K^-> 的 honest signature 是 (1; []; l)，χ = -l；
    C_K^-> := X_K^->/{±1} 的 honest signature 是 (0; [2,2,2]; (l+1)/2)，
    χ = -l/2。

证明.
(i) X_K^-> → X_K 由 isogeny E_K^-> → E_K（kernel 是 E_K[l] 的 order-l
subgroup）给出；它是 unramified，X_K^-> = E_K^-> 挖掉 O 上的 l 个点。
故 genus 1，l 个 cusps，signature (1; []; l)，χ = 2 - 2 - l = -l。
(ii) ±1 在 E_K^-> 上的作用为 -1。它在 4 个 2-torsion 点上固定；origin O'
是 cusp，另外 3 个 2-torsion 点不是 cusp，给出 3 个 order-2 stacky points。
在唯一的 cusp O 上的 l 个点中，O' 固定，其余 l-1 个被 ±1 两两配对，故
C_K^-> 的 punctures = 1 + (l-1)/2 = (l+1)/2。
(iii) 在 2-torsion 点 q 上的 l-point fiber 上，lift 的作用是 x ↦ -x（不是
trivial 的 translation：-1 把 isogeny 的 deck group 共轭为 inverse），所以
恰有 1 个 fixed point（唯一的 2-torsion lift），其余 (l-1)/2 个是 free orbits；
它们不产生额外 stacky points 或 punctures。
(iv) 因此 C_K^-> 的 coarse space 是 P^1，3 个 order-2 stacky points，
(l+1)/2 punctures；χ = 2 - (l+1)/2 - 3/2 = -l/2。
独立检验：X_K^-> → C_K^-> 是 degree-2 torsor，χ(X_K^->) = 2·χ(C_K^->)
= -l；C_K^-> → C_K 是 degree-l etale cover，χ(C_K^->) = l·χ(C_K) = -l/2；
X_K^-> → X_K 是 degree-l etale cover，χ(X_K^->) = l·χ(X_K) = -l。全部一致。
QED.

### 2.4 表：论文对象与 honest signature

| 对象 | 论文定义 | honest signature | χ |
|---|---|---|---|
| X_F | Def 3.1(b): (1,1) | (1; []; 1) | -1 |
| C_F | Def 3.1(b): [X_F/{±1}] | (0; [2,2,2]; 1) | -1/2 |
| X_K | X_F ×_F K (core) | (1; []; 1) | -1 |
| C_K | C_F ×_F K (core) | (0; [2,2,2]; 1) | -1/2 |
| X_K^-> | type (1,l-tors) | (1; []; l) | -l |
| C_K^-> | type (1,l-tors)^± | (0; [2,2,2]; (l+1)/2) | -l/2 |

## 3. Lean 现状

### 3.1 signature 是自由 metadata

Iut/Foundations/Orbicurve.lean:

* 58-106: OrbicurveSignature = (genus, stackyOrders, punctures)；
  eulerCharacteristic = 2 - 2g - n - Σ(1 - 1/m)；IsHyperbolic := χ < 0。
* 108-120: EtaleStackOverField.orbicurveSignature : Option OrbicurveSignature
  := none。这是字段，不是由 fiber 算出的。
* 377-399: OrbicurveGeometry 的 realizes_signature 只是
  stack.orbicurveSignature = some signature；signature_eq 说明同一个 stack
  不能有两个不同 signature，但不限制 signature 的数值。
* 401-422: HyperbolicOrbicurve.signature := geometry.signature。

LeanFormal/IUT/IUTI/HodgeTheater/SourceClauseAssemblyUnitsReduction.lean
386-420: realizedHyperbolicOrbicurve 把任意 signature（只要 hyperbolic）
插入 stack；signature 是构造参数，不是几何结果。

因此本审计的"标签错误"不会产生 Lean 矛盾；反过来，也不能从 Lean 的
HyperbolicOrbicurve.signature 读出商空间的几何。

### 3.2 四个标签

LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:

* 289-293: sourceTypeOneOne = (1; []; 1)。
* 295-303: sourceTypeOneOnePlusMinus = (1; [2]; 0)。**本审计的对象。**
* 305-313: sourceTypeOneLTorsion l = (1; [l]; 0)。
* 315-325: sourceTypeOneLTorsionPlusMinus l = (1; [2,l]; 0)。
* 327-366: 四条 hyperbolicity 定理；它们只检验 χ < 0，不检验几何。

sourceTypeOneOnePlusMinus 在生产 LeanFormal 中没有 D-clause 消费者
（仅在 SourceDefinition31Quantifiers.lean:295 定义、:331-334 的 hyperbolicity
定理中使用）；使用它的是 tmp/sheaf/xif/paper 的 paper-target 链
（S1881D9D7bActual.lean:157-183 的 S1881CF / S1881D9OrbicurveSlot,
S1886D9OrbicurveActual.lean:455, S1932SignActionQuotientActual.lean:264,
S1964QuotientCFActual.lean:348-351, 449, S1889D8RealCuspActual.lean:464-472），
以及 S1370/S1374 的 signature-typing 修复记录
（S1370SourceSignQuotientFix.lean:213, S1374SourceSignQuotientFix.lean:243）。

### 3.3 两套 C_F 标签

paper-target 链：

* S1932SignActionQuotientActual.lean:259-264:
  S1932CFQuotient 的 cF_signature : cF.signature = sourceTypeOneOnePlusMinus。
* S1886D9OrbicurveActual.lean:450-455:
  S1886PaperCF 的 cF_signature : cF.signature = sourceTypeOneOnePlusMinus。
* S1964QuotientCFActual.lean:433-456:
  S1964CFQuotientAt l A s hs，S1964CFQuotientAt_iff_paper 说明
  paper target 就是 s = sourceTypeOneOnePlusMinus 的实例。
* S1881D9D7bActual.lean:157-183: S1881CF 与 S1881D9OrbicurveSlot。
  slot 的字段是 cF、core : SourceOrbicurveScalarExtension F K cF、
  cK = core.result、xK、coverMap : xK.Hom cK；标签是
  cF = (1,1)^±、cK = (1,l-tors)^±、xK = (1,l-tors)。注意 cK 被定义成
  core.result（即 C_F 的 scalar extension = K-core），但标签却是 l-tors
  商；这是对象错位在 paper-target 侧的同一表现。coverMap 是 xK → cK，
  而论文的图是 X_K^-> → X_K 与 C_K^-> → C_K（不是 X_K^-> → C_K，除非
  先把 cK 误认为 C_K^->）。
* S1881D9D7bActual.lean:78-151 已证明 oncePuncturedElliptic（X_F 的
  signature）与三个标签都不等，并且 S1726Orbicurve 不是 C_F/C_K/X_K。
  这证明 actual X_F 不是商对象，但不提供 C_F 的 honest signature；
  honest signature 由 S1964 给出。
* S1889D8RealCuspActual.lean:464-472: S1889FirstMissing := S1881CF，
  即 missing 的第一对象被定义为带 (1,1)^± 标签的 C_F。

生产 source 契约：

* SourceInitialThetaData.lean:1859: cF_type :
  cF.signature = SourceOrbicurveSignature.typeOneOne。
* SourceInitialThetaData.lean:3331: clause_d_cF_signature 同上。
* SourceDefinition31D5D8Root.lean:283-285: d6_cF_signature 同上。
* Definition31D0D11Aligned.lean:743-745: cF_signature 同上。

所以树里对同一个 C_F 有两个互相冲突的 Lean 标签：
(1; [2]; 0) 和 (1; []; 1)。两者都不是 (0; [2,2,2]; 1)。

### 3.4 SourceSignQuotientData 的 cF_genus = 1

SourceDefinition31Quantifiers.lean:578-631: SourceSignQuotientData 没有 cF
signature 字段；cK 是 cKExtension.result（即 cF 的 scalar extension），
xK 是 xKExtension.result。标签是：

* 610: xKType : xK.signature = sourceTypeOneLTorsion l
* 611: cKType : cK.signature = sourceTypeOneLTorsionPlusMinus l
* 612-613: xK = xKExtension.result, cK = cKExtension.result

654-689: xK_signature / cK_signature 直接返回上述字段；
cF_genus : S.cF.signature.genus = 1 由 cKExtension.genus_preserved 和
cKType 推出。这个 genus 1 与论文强制的 genus 0 冲突；
任何 SourceSignQuotientData 的 inhabitant 都有这个 metadata。

### 3.5 文档里的根因误读

SourceDefinition31Quantifiers.lean:468-479（SourceOrbicurveScalarExtension
的 docstring）写道：

    The K-side objects of type (1,l-tors) and (1,l-tors)^± are obtained from
    the K-core by extracting l-th roots of the theta function ([EtTh],
    Definition 2.1), which adds l-torsion stacky structure over K. Thus the
    stacky orders and the punctures need not agree with the F-side signature.

"adds l-torsion stacky structure" 是误读：[EtTh] 的 l-tors 构造增加的是
cusps（对 cusp 上取 l-th root）与 cusp 上的 Z/l-torsor 标签，不是 inertia
group / stacky point。这一句就是 (1; [l]; 0)、(1; [2,l]; 0) 标签的来源。

### 3.6 S1964 的 actual 模型结论

tmp/sheaf/xif/paper/S1964QuotientCFActual.lean:

* 113: S1964Cubic_factors: x^3 + (61/64)x^2 - (125/64)x
  = x(x-1)(x + 125/64)。
* 120: S1964Equation_neg125: (-125/64, 0) 满足 Weierstrass 方程。
* 213: S1964Section_fixed_iff: 仿射模型的一个 section 被实际 [-1]
  endomorphism 固定 iff y = 0。
* 226: S1964TwoTorsion_abscissa: 所有 y = 0 的仿射点的 x 只能是
  0, 1, -125/64。
* 252: S1964Neg_eq_self_iff: negation 固定 p iff p.2 = 0。
* 266: S1964FixedPoint_cases: 实际 involution 的 fixed affine points
  恰是 (0,0), (1,0), (-125/64,0) 三个 2-torsion 点。
* 326-334: S1964HonestQuotientSignature = (0; [2,2,2]; 1)。
* 336-344: S1964HonestQuotientSignature_euler = -1/2；hyperbolic。
* 347-351: S1964HonestSignature_ne_paper:
  S1964HonestQuotientSignature ≠ sourceTypeOneOnePlusMinus。
* 355-368: S1964CoarseQuotientSignature = (0; []; 1)，χ = 1，不 hyperbolic。
* 377-389: S1964SignatureLabelsNotDeterminedByFiber:
  同一个 etale stack fiber 上可以有两个不同 signature 的
  HyperbolicOrbicurve（paper label vs honest label）。
* 396-403, 465-500: S1964QuotientStructure / S1964FirstMissing；
  S1964CFQuotientAt_iff_paper 说明 paper target 是
  s = sourceTypeOneOnePlusMinus 的实例；S1964FirstMissing_ofHonest
  说明 honest label 的 target 归约到同一个 quotient structure。

实际模型 S1726：E'/F'，F' = SplittingField (S1687H · (X^2 + 1))
（S1726OrbicurveFPrimeActual.lean 头部 21-29）；E':
y^2 = x^3 + (61/64)x^2 - (125/64)x（同文件 167-183）。
S1964 的上述定理把这个模型上的 2-torsion、固定点、honest signature 全部
形式化，且 kernel/axiom 审计为允许的 trio（见 S1964_report.md）。所以
"actual model" 一侧没有剩余歧义。

## 4. 对照与结论

### 4.1 论文预期 vs actual model

| | 论文预期 | actual S1726 model | Lean 标签 |
|---|---|---|---|
| C_F signature | (0; [2,2,2]; 1) | (0; [2,2,2]; 1)（S1964） | (1; [2]; 0) 或 (1; []; 1) |
| C_F χ | -1/2 | -1/2（S1964） | -1/2（巧合）或 -1 |
| C_F hyperbolic | yes | yes（S1964） | yes（两者都 hyperbolic） |
| C_K core signature | (0; [2,2,2]; 1) | 未单独构造（= C_F × K） | (1; [2,l]; 0) |
| C_K^-> signature | (0; [2,2,2]; (l+1)/2) | 未构造 | 无对象 |
| X_K core signature | (1; []; 1) | 未单独构造（= X_F × K） | (1; [l]; 0) |
| X_K^-> signature | (1; []; l) | 未构造 | 无对象 |

结论：论文预期 = actual model（在 C_F 上由 S1964 形式化）；Lean 标签是
outlier。由于 signature 是 metadata，"outlier" 不是 Lean 的矛盾，而是
paper-faithfulness 的失败：一个 honest 的 C_F 不能填
S1932CFQuotient.cF_signature（除非改 target 或用 S1964CFQuotientAt 的
honest 参数）。

### 4.2 转录错误 vs 对象错位

两者都有，且发生在不同位置：

(A) **转录错误（C_F 标签）**：sourceTypeOneOnePlusMinus = (1; [2]; 0) 把
[EtTh] 的构造类型 (1,1)^± 读成数值 signature。^± 是 "对 ±1 取 stack 商"，
不是 "加一个 order-2 stacky point"；被商曲线的 (1,1) 也不是商空间的
(genus, punctures)。正确值是 (0; [2,2,2]; 1)。生产 D-clause 的
typeOneOne = (1; []; 1) 则是另一个转录错误：把 C_F 与 X_F 混同
（同一个标签同时用于 xF 和 cF）。

(B) **对象错位（K 侧标签）**：SourceSignQuotientData 的 xK/cK 是
K-core（xK = xKExtension.result, cK = cKExtension.result），但被贴上
sourceTypeOneLTorsion / sourceTypeOneLTorsionPlusMinus 这两个论文
type (1,l-tors) / (1,l-tors)^± 覆叠的标签。论文的这四个 K 侧对象
（X_K, C_K, X_K^->, C_K^->）在契约里只有前两个（且作为 base change），
后两个不存在。即使把标签当作覆叠对象的 signature，数值也错：
(1; [l]; 0) ≠ (1; []; l)，(1; [2,l]; 0) ≠ (0; [2,2,2]; (l+1)/2)。

(C) **误读根因**：SourceOrbicurveScalarExtension 的 docstring
（Quantifiers:468-479）声称 l-tors 构造 "adds l-torsion stacky structure"。
[EtTh] Def 2.1 的构造是 degree-l covering + ±1 quotient；X_K^-> 有 l 个
cusps（不是 stacky order-l point），C_K^-> 的 stacky 结构仍然只有 3 个
order-2 points（来自 2-torsion），只是 punctures 变成 (l+1)/2。

### 4.3 为什么没有 Lean 矛盾；χ 巧合

* signature 是自由字段（3.1），所以任何 (genus, stackyOrders, punctures)
  都可以被 realizedHyperbolicOrbicurve 插入；没有定理把它与 fiber 的几何
  联系起来。S1964SignatureLabelsNotDeterminedByFiber 直接把这一点用于
  paper label vs honest label。
* cF_genus = 1 是关于该字段的定理（由 cKType 和 genus_preserved 推出），
  不是关于 C_F 的几何定理；它使 SourceSignQuotientData 的任何 inhabitant
  都带 genus-1 metadata，因而不能与 honest C_F 相容（本审计 Lean 文件的
  sourceSignQuotientData_cF_ne_paperCF）。
* χ 巧合：错误标签 (1; [2]; 0) 的 χ = 2 - 2 - 0 - (1 - 1/2) = -1/2，
  与 honest (0; [2,2,2]; 1) 的 χ = 2 - 0 - 1 - 3/2 = -1/2 相同。
  因此 hyperbolicity / χ 测试完全无法发现该错误。其它生产标签连 χ 都不对：
  cF 的 (1; []; 1) χ = -1；xK 的 (1; [l]; 0) χ = -1 + 1/l；cK 的
  (1; [2,l]; 0) χ = -3/2 + 1/l。若把"标签的 χ 必须等于对象的 orbifold χ"
  作为审计条件，三条 K/F 标签会立即失败，只有 (1; [2]; 0) 因数值巧合通过。

### 4.4 逐标签判定

| Lean 声明 | 值 | 声称对象 | honest 值 | 判定 |
|---|---|---|---|---|
| sourceTypeOneOnePlusMinus | (1; [2]; 0) | C_F | (0; [2,2,2]; 1) | 错（转录） |
| SourceOrbicurveSignature.typeOneOne（用于 cF） | (1; []; 1) | C_F | (0; [2,2,2]; 1) | 错（C_F/X_F 混同） |
| sourceTypeOneLTorsion l | (1; [l]; 0) | X_K core 或 X_K^-> | (1; []; 1) 或 (1; []; l) | 错（对象错位 + 数值） |
| sourceTypeOneLTorsionPlusMinus l | (1; [2,l]; 0) | C_K core 或 C_K^-> | (0; [2,2,2]; 1) 或 (0; [2,2,2]; (l+1)/2) | 错（对象错位 + 数值） |
| sourceTypeOneOne（用于 xF） | (1; []; 1) | X_F | (1; []; 1) | 对 |

## 5. Exact missing

不是"改一个数字"就能闭合的。精确缺口：

(M1) 商 stack。S1964 的 S1964FirstMissing l A :=
Nonempty (S1964QuotientStructure l A)；其第一 missing field 是
category-valued etale stack 的构造：pointwise lax colimit / 函子性与相干 /
Pseudofunctor.IsStack（stackification）/ 双范畴普遍性（S1964_report.md 的
四步）。在构造之前，任何 C_F signature 都只是 label，不能作为几何断言。

(M2) [EtTh] 类型名的形式化桥。当前 Lean 只有裸的 OrbicurveSignature，
没有定义 "type (1,1)^±" / "type (1,l-tors)" / "type (1,l-tors)^±" 这些
构造类型，也没有定理把它们与 (0; [2,2,2]; 1) / (1; []; l) /
(0; [2,2,2]; (l+1)/2) 连接。要做 paper-faithful 的签名审计，这个桥是
第一等的 missing declaration；它不能由 axiom 代替。

(M3) K 侧覆叠对象。paper 的 X_K^->, C_K^-> 在 Lean 契约中没有字段；
SourceSignQuotientData 只有 xK/cK（core）。加入这两个对象是定义/结构
变更（需要 lead 批准），不是本审计的范围。

(M4) 现有标签/target 的处置。sourceTypeOneOnePlusMinus 目前被
S1881CF/S1881D9OrbicurveSlot / S1932CFQuotient / S1886PaperCF /
S1964CFQuotientAt / S1889FirstMissing 使用；改它会改变这些 target 的
elaborated type。生产 D-clause 的 cF/cK/xK 标签也有下游
（SourceDefinition31D5D8Root, Definition31D0D11Aligned, SourceCompletion,
SourceGeometricCoreFieldUnitsReduction 等）。是否改 target、改标签、还是
保留为 metadata 并加审计注记，是目标锁定层面的决定；本审计只报告，
不擅自改定义，也不把 (0; [2,2,2]; 1) 直接塞进 sourceTypeOneOnePlusMinus。

明确不做的事：

* 不把 sourceTypeOneOnePlusMinus 悄悄改成 (0; [2,2,2]; 1)；
* 不加 axiom / opaque bridge 让标签"自洽"；
* 不把 coarse quotient (0; []; 1) 当作 C_F（χ = 1，不 hyperbolic）；
* 不把 cF_genus = 1 或 cK/xK 的标签当作几何证据。

## 6. Lean audit 文件与验收

文件：tmp/sheaf/s1972/S1972CFSignatureAudit.lean
（426 行，17550 bytes，SHA256 EFFCF24C401EA01F74DC29602DA4B84F85B4254E13ECEE9BF3955B5CC6E3A879）

编译：

    lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/s1972/S1972CFSignatureAudit.olean tmp/sheaf/s1972/S1972CFSignatureAudit.lean

结果：EXIT = 0；无 error、无 warning、无 sorry/admit/axiom。
olean：.lake/build/lib/lean/tmp/sheaf/s1972/S1972CFSignatureAudit.olean
（312584 bytes，SHA256 CCB2D197E3C350FB33A362A23CA15B0C810876E7584D4492C64662856313F071）。
日志：tmp/sheaf/s1972/S1972_compile.log。
#print axioms 的输出只含 propext, Classical.choice, Quot.sound
（部分 declaration 只含 propext；见日志）。

关键声明：

* paperCF := S1964HonestQuotientSignature；(0; [2,2,2]; 1)，χ = -1/2。
* paperLabelCF := sourceTypeOneOnePlusMinus；(1; [2]; 0)，χ = -1/2。
* paperLabelCF_ne_paperCF：genus 1 ≠ 0。
* paperLabelCF_euler_eq_paperCF：χ 相同（-1/2），说明 χ 无法区分。
* paperCF_euler_two_mul：2·χ(C_F) = χ(X_F) = -1。
* legacyTypeOneOne_ne_paperCF：D-clause 的 cF 标签 (1; []; 1) ≠ honest。
* paperLabelCF_ne_legacyTypeOneOne：树里的两个 C_F 标签也互相冲突。
* honestXKTors / honestCKTors：K 侧 honest signatures (1; []; l) /
  (0; [2,2,2]; (l+1)/2)；χ 分别为 -l / -l/2；均 hyperbolic。
* honestXKTors_euler_eq_l_mul_oncePunctured、
  honestCKTors_euler_eq_l_mul_paperCF、
  honestXKTors_euler_eq_two_mul_honestCKTors：degree-l / degree-2 cover 的
  χ 关系。
* legacyTypeOneLTorsion_ne_honestXKTors、
  legacyTypeOneLTorsionPlusMinus_ne_honestCKTors、
  legacyTypeOneLTorsionPlusMinus_ne_paperCF：K 侧标签与 honest 值不符。
* sourceSignQuotientData_cF_genus：任意 SourceSignQuotientData 的
  cF.signature.genus = 1。
* sourceSignQuotientData_cF_ne_paperCF：因此生产契约的 cF metadata 不能是
  honest C_F 的 signature。
* sourceSignQuotientData_cK_ne_paperCF：
  cK 标签 (1; [2,l]; 0) ≠ (0; [2,2,2]; 1)。
* sourceSignQuotientData_xK_ne_oncePunctured：
  xK 标签 (1; [l]; 0) ≠ (1; []; 1)。
* sourceSignQuotientData_xF_eq_oncePunctured：xF 标签是正确的（对照）。
* exactMissing_iff_quotientStructure：S1964FirstMissing l A ↔
  Nonempty (S1964QuotientStructure l A)。

验收状态：

    statement_compiles: yes（EXIT 0）
    proof_body_checked: yes（无 sorry；所有声明已证）
    kernel_closed: yes（对 audit 文件的 #print axioms 而言，仅 trio）
    target_accepted: not applicable / no（本文件是审计，不是锁定 target；
                     商构造仍缺，见第 5 节）

## 7. 未改定义声明与下一步

* 未编辑生产 Lean 文件；未改 SourceDefinition31Quantifiers.lean 的任何定义；
  未新增 axiom/sorry。
* 本审计新增 tmp/sheaf/s1972/S1972CFSignatureAudit.lean 与
  coord/reports/S1972CFSignatureAudit.md，并在 coord/STATE.md 末尾追加一条
  S1972 记录；未触碰任何生产 Lean 文件。
* 工作树里 SourceDefinition31Quantifiers.lean 显示为 modified，这是
  2026-10-30 22:22:49 的既有 S1370/S1374 修复（signature_preserved 改为
  genus-only），不是本审计的改动。
* 下一步（按优先级）：
  1. 把本报告的标签结论登记到 DAG/STATE/AUDIT_LEDGER；
  2. 若 lead 决定追求 paper-faithful target，先做 (M2) 的 [EtTh] 类型桥
     （definition + theorem，不用 axiom），再决定是否把
     sourceTypeOneOnePlusMinus 及 D-clause 的 cF/cK/xK 标签 retype；
     这需要 target 锁定层面的批准，并重新审视所有下游 consumers；
  3. 真正的数学缺口仍是 (M1) 的商 stack 构造；标签修正不能替代它。
