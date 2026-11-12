# HANDOFF-OBJECT-TABLE — R29/task-74 object table, coordinates, stop-lemma verdict

Snapshot: 2026-11-13 (Asia/Shanghai). Read-only audit; no compile; no assembly file.

Sources read first:
- coord/COR312-NORMALIZATION.md, TERM-TABLE.md, OUR-R-IDENTIFICATION.md,
  ACTUAL-FINALL-DATA-PLAN.md, MODEL-FIX.md, FINITE-DIM-VOLUME-PLAN.md, ENLARGEMENT-AUDIT.md;
- HANDOFF §1.4/§2/§3.7/§4.8 (body ends at §5.13; §6-12 absent).
- Lean declarations re-checked by content search and line reads, not by file-number guess.

## 0. Chosen real finite place tensor block

T : SourceNativeInitialThetaData.{0} l (LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1681).
b : Bad (nativePlaceSelection T).

E := qVFamTensorBlock T b
  = ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple
  (tmp/sheaf/xif/paper/QVFamTensorCoefficientActual.lean:72-73).

This is the actual one-factor finite p-adic tensor packet at the actual bad F-place
qVFamTensorPlace T b = (nativeBadLift T).lift b (:47), p = qVFamTensorP T b (:51),
places (:63), tuple (:69). It is finite-dimensional over Q_p. All objects below are
on this block unless explicitly marked otherwise.


## 0.1 HANDOFF §2 target and quantifier (used, not altered)

HANDOFF §2 locks M = A - R = V + gap - (sF-1)A >= 0, not the stronger
V - (sF-1)A >= 0. The quantifier is over actual initial Theta-data T satisfying the
locked source conditions, with every construction property coming from T or a closed
general theorem. This table keeps that shape: qVFamTensorBlock is built from T and b,
and no new positivity/size hypothesis is added to fill a cell. Unfilled cells are
listed as missing/named-input rather than replaced by True/PUnit/toy data.

## 1. HANDOFF §3.7 object table

| 项目 | 精确 Lean 名字 | file:line | 证据等级 | 备注 / 不能接受的替代 |
|---|---|---|---|---|
| 原输入 | T : SourceNativeInitialThetaData.{0} l | LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1681 | actual | 不是任意弱数据类；保留真实数域/曲线/坏位数据 |
| 有限位载体 E | qVFamTensorBlock T b = ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple | QVFamTensorCoefficientActual.lean:72-73 | actual | 单因子 Unit 索引；不是未证明等价的另一域 |
| 载体底域/位 | qVFamTensorP T b (:51), qVFamTensorPlace T b (:47), qVFamTensorPlaces (:63) | 同文件:47/51/63 | actual | p 为实际剩余特征；不是任选 p |
| theta 可能像（paper 非零标签） | paperRootThetaImageNZ = ⋃ j : PaperNonzeroLabel, paperRootThetaRegionNZ j | S793PaperLeastLambdaOHullActual.lean:79-80; region :73-77; PaperNonzeroLabel :44 | actual | 非零标签并；每个 region 是 paperLambdaORegion（:65-70） |
| theta 可能像（当前 root 定义） | rootThetaImageSet = ⋃ j : SignedLabel, rootThetaRegion j; rootThetaHull = closure rootThetaImageSet | RootHullContainmentInequalityActual.lean:73-79 | actual + model deviation | 用 SignedLabel（含 j=0）；j=0 系数为 0，见 §4.8 |
| 允许作用 Ind1 | ind1Act (e : Equiv.Perm (SignedLabel l)) on SignedLabel → S1902Carrier; ind1Images | Mzk1ThetaPilotObjectActual.lean:84-87, :104-105 | actual, different carrier | 作用在 S1902Carrier，不在 qVFamTensorBlock；块级作用 missing |
| 允许作用 Ind2 | ind2Act (ζ : rootsOfUnity (2l) in rootNormedExtension); ind2Images | 同文件:90-94, :108-110 | actual, different carrier | 同上；不是全 GL_d 任挑矩阵 |
| 允许作用 Ind3 | ind3Act (u : (rootNormedExtension)ˣ); ind3Images | 同文件:98-101, :113-115 | actual, different carrier | 乘 root-extension 单位；块级 Ind3 action 未构造 |
| Ind3 输出 hull | ind3OutputHull := rootNormHull (qVFam block) | Ind3OutputHullQPilotActual.lean:70-71 | actual (model closure) | 是 root hull closure，不是 stage-level image |
| Ind3 stage → output hull | Ind3StageToOutputHullGap (stageImage/ stageImageToOutputHull/ log-compatible) | Ind3OutputHullQPilotActual.lean:156-164 | named-input/missing | 无实际 stage-to-region multiradial map；不得用值层/包围替代 |
| 整数基准 R | R := arithmeticTupleValuationIntegerLattice places tuple = tensorIntegerLattice | FinitePlaceIntegerTensorComparison.lean:32-35 | actual | 各因子整数环张量；不是 O_E |
| 整数基准 O_E | O_E := arithmeticTupleValuationIntegerNormalization = integralClosure Zp (ArithmeticTensorTupleBlock ...) | IntegralTraceDualTensorInclusion.lean:494-496 | actual | R 在张量中的整闭包；不是 R |
| 整数基准 L_log | L_log := arithmeticTupleIntegralLogLattice = tensorLogShellLattice | FinitePlaceIntegralLogTensorLattice.lean:26-28 | actual | log-shell 张量格；不等同单位球 |
| 整数关系 | R ⊆ O_E: arithmeticTupleValuationIntegerLattice_le_normalization | IntegralTraceDualTensorInclusion.lean:514-519 | actual | — |
| 整数关系 | R ⊆ L_log: tensorIntegerLattice_le_logShellLattice | FinitePadicIntegerTensorLattice.lean:95-97 | actual | — |
| 整数关系 | O_E vs L_log relation/equality | — | missing | 树内无 O_E ⊆ L_log 或反向定理；不能统称单位球 |
| q 对象 | qVFamily T b : FinitePlaceQCandidate ((nativeBadLift T).lift b) | QPilotZeroLocusDivisorActual.lean:55-62 | actual | clause-B Tate comparison 参数；不是为结论做的球 |
| q 根 | qThetaRoot T b : rootNormedExtension T b; qThetaRoot_pow: qroot^(2l)=q | Mzk1ThetaPilotObjectActual.lean:52-62 | actual | 真实根扩域元素 |
| q 根扩域 | rootNormedExtension T b = IntermediateField.adjoin (rootBase) {rootNormedElement} | PaperRootCompletionTensorActual.lean:58-60; rootNormedElement :54 | actual | 有限中间域，不是 FinalL=AlgebraicClosure |
| q 归一化系数 | qVFamNormalizedCoefficient = qVFamTensorCoefficient = order(qVFamily) | QVFamNormalizedCoefficientActual.lean:48-57 | actual | c_norm = m |
| paper q 系数 | qVFamPaperRootCoefficient = order(qVFamily)/(2l) | QVFamRootFactorCorrectionActual.lean:56-57 | actual | c_root = m/(2l) |
| paper theta 系数 | qVFamPaperThetaTensorCoefficient j = j^2 * order/(2l) | QVFamRootFactorCorrectionActual.lean:59-63 | actual | 随 m 线性 |
| q-pilot region (paper half) | qPilotPaperRegion = thetaTensorScaledRegion rootHalfCoefficient | S800LeastLambdaOHullActual.lean:76-78 | actual | 与 qPilotPaperRegion_eq_rootThetaRegion_one :80-88 |
| q-pilot region (classical c_norm) | qPilotNormRegion = qPilotClassicalRegion rootNormCoefficient | RootNormalizedContainmentActual.lean:83-85 | actual, model normalization | c_norm=m, 不是 paper 的 m/(2l) |
| theta hull (paper coefficient) | paperRootThetaHull b = rootThetaHull (paperRootCoefficientFamily) | BadPlacePaperRootThetaHullActual.lean:40-43; coefficient :36-38 | actual definition, model hull | 用 rootThetaHull，含 SignedLabel 的 j=0，见 §4.8 |
| 读数 theta (finite block) | paperRootThetaHullLog b mu = rootThetaHullLog ... paperRootCoefficientFamily | BadPlacePaperRootThetaHullActual.lean:45-49 | actual definition | 精确公式条件式于 PaperRootHullFormulaGap :56-66 |
| 读数 q (finite block) | qPilotPaperRegionLog = arithmeticTupleNormalizedLogVolume ... qPilotPaperRegion | S800LeastLambdaOHullActual.lean:116-118 | actual definition | 以 c_root 归一化；q 公式未在树内给出 |
| 读数分母 | arithmeticTupleNormalizedLogVolume = (1/d) log(mu S / mu canonical unit ref) | FinitePlaceNormalizedUnitScalingLogVolume.lean:92-99 | actual | 1/d 是维数归一化，不是 paper procession weight |
| 权重 | nativeBadLocalWeight b = localNormalizedWeight (nativeBadToKPlace b) | VbadPlaceIndexingActual.lean:89-91; formula :94-97 | actual | 只给坏位有限权重；procession/j 权重 missing |
| 支撑 | Bad/nativePlaceSelection finite; SignedLabel finite; paperRootThetaImageNZ finite union | Fintype instances; S793:79 | actual | 有限坏位支撑；全位置/arch 支撑 missing |
| 无穷位 | RationalPlace.infinite exists in Cor312/RationalPlace; no arch region/measure on qVFam block | Iut/Cor312/RationalPlace.lean:34; — | missing | qVFam block is one finite place; gamma_q/gamma_theta arch terms not constructed |
## 2. HANDOFF §1.4 five-coordinate table

| 坐标 | 精确 Lean 对象/公式 | file:line | 证据等级 | 备注 |
|---|---|---|---|---|
| 1. 原始 theta 生成元坐标 | qThetaValue j b = (qThetaRoot T b)^(gaussExponent j); qThetaRoot^(2l)=q | Mzk1ThetaPilotObjectActual.lean:52-71 | actual | 在 rootNormedExtension T b 中；另一实现 paperRootThetaImagePoint : PaperC3ThetaRootActual.lean:75-77 |
| 2. 允许像坐标 | qThetaVector : SignedLabel → S1902Carrier; ind1Act/ind2Act/ind3Act | Mzk1ThetaPilotObjectActual.lean:81, :84-101 | actual, different carrier | 作用于 S1902Carrier；无实际 map 到 qVFamTensorBlock |
| 3. R vs O_E vs L_log | R=arithmeticTupleValuationIntegerLattice; O_E=arithmeticTupleValuationIntegerNormalization; L_log=arithmeticTupleIntegralLogLattice | FinitePlaceIntegerTensorComparison.lean:32; IntegralTraceDualTensorInclusion.lean:494; FinitePlaceIntegralLogTensorLattice.lean:26 | actual | 仅 R⊆O_E 与 R⊆L_log 已证；O_E vs L_log missing |
| 4. 实际 q 读数 | qVFamily; qVFamPaperRootCoefficient=order/(2l); qPilotPaperRegionLog | QPilotZeroLocusDivisorActual.lean:55; QVFamRootFactorCorrectionActual.lean:56; S800:116 | actual | qPilotNormRegion/classical 用 c_norm=order，不是 paper c_root；见 §4.8 |
| 5. 原文权重/维数归一化 | arithmeticTupleNormalizedLogVolume = (1/d)log(mu S/mu canonical ref); nativeBadLocalWeight=1/localCompletionDegree | FinitePlaceNormalizedUnitScalingLogVolume.lean:92; VbadPlaceIndexingActual.lean:89 | actual (dimension); weight finite bad only | 1/d 是局部记账；procession j-weight/sF 未在此块构造 |

## 3. HANDOFF §4.8 — does the common-scalar stop lemma cover the actual Theta hull?

### 3.1 Definitions and exact scaling

- qVFamily.order = m (not a name but the actual order field).
- qVFamNormalizedCoefficient T b = qVFamTensorCoefficient T b = m
  (QVFamNormalizedCoefficientActual.lean:48-57, rfl).
- qVFamPaperRootCoefficient T b = m/(2l)
  (QVFamRootFactorCorrectionActual.lean:56-57).
- qVFamPaperThetaTensorCoefficient j = j^2 * m/(2l)
  (QVFamRootFactorCorrectionActual.lean:59-63).
- rootHalfCoefficient = rootNormCoefficient/(2l) = m/(2l)
  (RootNormalizedContainmentActual.lean:57-58).
- thetaTensorScaledRegion c = F(c) * O_hol, with F(c)=arithmeticTupleFractionalLattice c
  (ThetaTensorScaledImageActual.lean:55-60); F is antitone: c<=d => F(d) <= F(c)
  (FinitePlaceFractionalTensorLattice.lean:113-120).
- rootThetaImageSet = union over SignedLabel of F(j^2 c_root)*O_hol
  (RootHullContainmentInequalityActual.lean:73-75; rootThetaCoefficient :73-75).
- rootThetaHull = closure rootThetaImageSet (RootHullContainmentInequalityActual.lean:78-79).

### 3.2 The zero-label contamination in rootThetaHull

SignedLabel l = {j : Int // -l* <= j <= l*} (GaussianKernel.lean:94-95), so j=0 is included.
gaussExponent 0 = 0 (GaussianKernel.lean:30). Therefore rootThetaRegion at j=0 has
coefficient 0, and thetaTensorScaledRegion (fun _ => 0) = F(0)*O_hol;
arithmeticTupleFractionalLattice_zero says F(0)=arithmeticTupleValuationIntegerLattice=R
(FinitePlaceFractionalTensorLattice.lean:54-61).
Thus rootThetaHull contains R*O_hol, a q-independent set. rootThetaHull is NOT a single
p^{a(m)} times a fixed lattice; its q-dependence includes a fixed component and a
nonzero-label component. Consequently the common-scalar stop lemma does not apply to
the actual rootThetaHull definition as written.

### 3.3 The paper-nonzero image and the stop lemma

paperRootThetaImageNZ uses PaperNonzeroLabel (S793:44, :79-80), i.e. j != 0.
For j != 0, j^2 >= 1, and F is antitone, so every F(j^2 c_root) is contained in
F(c_root); the j=+/-1 term realizes F(c_root). Hence
  paperRootThetaImageNZ = F(c_root)*O_hol
is a common-scalar family with a(m)=c_root=m/(2l). The §4.8 hypothesis holds for
the lattice part: all images are p-scales of the fixed O_hol (up to the actual
fractional-lattice convention). The conclusion is that the index relative to the
common scalar is independent of a(m); no unbounded m-linear *relative* gain arises
from this common-scalar mechanism.

Caveat: absolute normalized log-volume still has the linear term from a(m):
arithmeticTupleNormalizedLogVolume of F(c_root)*O_hol is linear in c_root, hence in m.
The stop lemma excludes relative index gain, not the common linear volume shift.

### 3.4 q-side normalization conflict

paper q region qPilotPaperRegion (S800:76) also uses rootHalfCoefficient c_root=m/(2l);
it is exactly F(c_root)*O_hol (qPilotPaperRegion_eq_rootThetaRegion_one :80-88).
But the green Ind3 comparison uses actualQPilotLogShellRegion = qPilotNormRegion
(Ind3OutputHullQPilotActual.lean:74; RootNormalizedContainmentActual.lean:83), whose
coefficient is rootNormCoefficient=c_norm=m, not c_root=m/(2l). Its qPilotClassicalLog
formula is -m log p (RootHullContainmentInequalityActual.lean:111-114), not paper
-m/(2l) log p. Therefore the green inequality
qPilotClassicalLog <= rootThetaHullLog (RootNormalizedContainmentActual.lean:123;
Ind3OutputHullQPilotActual.lean:97) compares the c_norm q-region with the c_root hull;
it is not the paper |log q| <= -|log Theta| comparison.

### 3.5 Verdict on §4.8

- Actual rootThetaHull as defined (RootNormalizedThetaHullActual:89) includes j=0 and
  contains the q-independent R*O_hol; it is not a common-scalar family. The stop lemma
  does not cover this definition, and its conclusion cannot be used to rule out m-growth
  for it.
- The paper-nonzero image paperRootThetaImageNZ is a common-scalar family F(c_root),
  c_root=m/(2l); for that family the §4.8 stop lemma applies: relative index is m-independent.
- paperRootThetaHull (BadPlacePaperRootThetaHullActual:40) is built from rootThetaHull
  (the zero-label version), so it inherits the zero-label contamination; it is not proved
  equal to the paper-nonzero hull. Exact equality is PaperRootHullFormulaGap (:56-66), missing.
- The only source of a genuine m-linear *comparison gain* would be Ind2/Ind3 enlargement
  (gap), but on this block there is no actual Ind action and no stage-to-output-hull map;
  Ind3StageToOutputHullGap (:156-164) is missing. Thus the current block cannot supply the
  gap needed for the paper variant.

## 4. Cells that cannot be filled without fabrication

| cell | why missing | exact evidence |
|---|---|---|
| 允许作用 on qVFamTensorBlock | Ind1/2/3 act on S1902Carrier / FinalLValuedCarrier, not on the finite block | Mzk1ThetaPilotObjectActual.lean:84-115; PaperFinalLValuedTensorCarrierActual.lean:71-74 |
| Ind3 stage image -> block hull | only Ind3StageToOutputHullGap Prop | Ind3OutputHullQPilotActual.lean:156-164 |
| O_E vs L_log | no inclusion/equality theorem | IntegralTraceDualTensorInclusion.lean:494; FinitePlaceIntegralLogTensorLattice.lean:26 |
| rootThetaHull = paper hull | zero label + closure; no equality | RootHullContainmentInequalityActual.lean:73-79; RootHullContainmentInequalityActual.lean:73-79 |
| paperRootThetaHull = minimal lambda-O region | PaperRootHullFormulaGap absent | BadPlacePaperRootThetaHullActual.lean:56-66 |
| paper q reading | qPilotNormRegion uses c_norm=m, paper uses c_root=m/(2l); no identification | RootNormalizedContainmentActual.lean:83; QVFamRootFactorCorrectionActual.lean:56 |
| arch/infinite contribution | no arch region/measure on qVFam block | RationalPlace.lean:34; qVFam block finite only |
| procession weight/sF | no actual weight/sF on this block; only native bad-local weight | VbadPlaceIndexingActual.lean:89; COR312-NORMALIZATION coefficient table |
| global two-reading (D) equality | only finite bad-part readings; no arch/gamma terms | S800:111-118; BadPlace...:45-54 |

## 5. Conflict handling with earlier tasks/notes

- COR312-NORMALIZATION claimed the paper-faithful union is the 'lit' union; the actual
  rootThetaHull uses SignedLabel incl. 0. The claim is correct for paperRootThetaImageNZ
  but not for rootThetaHull. This is recorded as a conflict/deviation, not silently resolved.
- S971/S979/S981 green chain is on FinalLValuedCarrier with an assumed measure and a
  closure tensorRegionHull; it is not this finite qVFam block and is not used here.
- OUR-R-IDENTIFICATION sourceSignedHullLogVolume is a different source-hull carrier; no
  identification with qVFam rootThetaHull is present; not used.
- FINITE-DIM-VOLUME-PLAN/MODEL-FIX recommend the qVFam finite block; this table follows that,
  and keeps FinalL non-finite as an obstruction (not a carrier).
- ENLARGEMENT-AUDIT's faithful E=gap is lana gap on a different carrier; gap is not
  constructed on the qVFam block, so it is not used as a cell value.
- A1118 coefficient table remains valid for sF and |log q| on the paper side, but it does
  not provide the qVFam block weights/actions; no rewiring.

## 6. Coverage count

§3.7 table: 31 data rows (including integer-relation subrows and two theta-image variants).
§1.4 table: 5 rows.
Missing/named-input cells listed: 9.
Matrix/action cells actual only on different carriers: Ind1, Ind2, Ind3.

## 7. Bottom line

The real finite block qVFamTensorBlock has actual q, root extension, R/O_E/L_log, actual
regions and actual normalized-volume readings. But the paper Theta-hull object is not
faithfully represented by rootThetaHull (zero label, closure, no equality to the paper
minimal hull), the allowed actions live on other carriers, and the Ind3 stage-to-block
map is missing. The public-scalar stop lemma does not cover rootThetaHull; it does cover
the nonzero common-scalar image paperRootThetaImageNZ, for which relative index is
m-independent. The paper comparison gain must come from Ind2/gap, which is exactly the
missing block-level structure.
## 8. Build evidence (existing olean presence; no new compile run)

Audit did not compile. The only build evidence used is existence of the mapped .olean under
.lake/build/lib/lean/tmp/sheaf/xif/paper/ (olean=YES) or absence (NO). This is not a proof
that the statement was gate/kernel-checked now; it is a snapshot of the existing build.

| cited file | olean |
|---|---|
| QVFamTensorCoefficientActual.lean | YES |
| S793PaperLeastLambdaOHullActual.lean | YES |
| RootHullContainmentInequalityActual.lean | YES |
| RootNormalizedContainmentActual.lean | YES |
| Ind3OutputHullQPilotActual.lean | YES |
| QVFamNormalizedCoefficientActual.lean | YES |
| QVFamRootFactorCorrectionActual.lean | YES |
| BadPlacePaperRootThetaHullActual.lean | YES |
| S800LeastLambdaOHullActual.lean | YES |
| VbadPlaceIndexingActual.lean | YES |
| QPilotZeroLocusDivisorActual.lean | YES |
| PaperRootCompletionTensorActual.lean | YES |
| Mzk1ThetaPilotObjectActual.lean | NO (source only) |
| FinitePlaceIntegerTensorComparison.lean | NO (source only) |
| IntegralTraceDualTensorInclusion.lean | NO (source only) |
| FinitePlaceIntegralLogTensorLattice.lean | NO (source only) |
| FinitePlaceNormalizedUnitScalingLogVolume.lean | NO (source only) |

NO means only that no mapped olean exists at audit time; it does not by itself assert a
mathematical failure. YES does not assert a current kernel/gate check of this audit's claims.

## 9. Report obligations

- Cited files/lines are in the tables above and in §3.1-§3.5.
- No compile was run; build evidence is the olean-presence snapshot in §8.
- No upper-level assembly file was created; only this note.
- All gaps are explicit missing/named-input; no toy/PUnit/True carrier was used.
## 10. Target-faithfulness addendum (task-83): paper's j-set is nonzero F_l^× / {±1}

Primary text (papers/motizuki_corpus/text, line numbers exact):

- IUT I, lines 153-162:
  l* = (l-1)/2, l± = (l+1)/2, F_l^⋇ := F_l^× / {±1}, F_l^⋊± := F_l ⋊ {±1}.
  Thus F_l^⋇ is the quotient of the **nonzero** elements F_l^×, cardinality (l-1)/2.
- IUT II, lines 125-130:
  j ∈ {0,1,...,l*}; |F_l| := F_l / {±1} = {0} ∪ F_l^⋇.
  So 0 is a separate label, not an element of F_l^⋇.
- IUT II, lines 285-292:
  'the label 0 corresponds to the [mono-analytic] core'; |F_l| = {0} ∪ F_l^⋇.
- IUT III, lines 4512-4519:
  the theta values q^{j^2}_v are indexed by j ∈ F_l^⋇ (they depend on these labels);
  the number-field copies F_mod are independent of these labels.

Conclusion (paper faithfulness):
- The Θ-pilot theta values use j ∈ F_l^⋇ = F_l^×/{±1}; j=0 is the core label, not a theta value.
- Our SignedLabel l = {j : Int // -l* <= j <= l*} (GaussianKernel.lean:94-95) includes j=0.
  Our rootThetaImageSet/rootThetaHull (RootHullContainmentInequalityActual.lean:73-79)
  unions over SignedLabel, so it includes j=0.
  At j=0, gaussExponent 0=0, rootThetaCoefficient=0, and thetaTensorScaledRegion 0
  is F(0)*O_hol = R*O_hol, q-independent. Hence rootThetaHull contains the q-independent
  R*O_hol and is NOT the paper Θ-hull. This is a model deviation, not a neutral closure choice.

Paper-faithful target statement:
  paperThetaHullNZ := closure (paperRootThetaImageNZ),
  where paperRootThetaImageNZ = union over j : PaperNonzeroLabel (j != 0)
  (S793PaperLeastLambdaOHullActual.lean:44, :79-80).
  It should be compared with paperLeastLambdaOHull (S793:91-92) and, if Ind images are included,
  with the closure of the actual Ind2/Ind3 enlarged image set.

What is missing / inconsistent:
- `paperRootThetaHull` (BadPlacePaperRootThetaHullActual.lean:40-43) is defined via rootThetaHull
  (the SignedLabel version with j=0), so it is not the paper-nonzero hull.
- Its `PaperRootHullFormulaGap` (BadPlacePaperRootThetaHullActual.lean:56-66) demands
  paperRootThetaHull = F(c_root)*O_hol. Since paperRootThetaHull contains R*O_hol and
  F(c_root) is a proper subset of R for c_root>0 (F antitone), the equality cannot hold
  unless R=F(c_root). Thus this gap is not merely unproved; as stated it is incompatible
  with the j=0 term. It must be repaired by redefining the hull over PaperNonzeroLabel
  (or by proving the zero term is absent), not filled by a proof.
- `paperRootThetaImageNZ_subset_minimal` (S793:94-96) gives only containment in the minimal
  region at c_root; the equality of the nonzero closure with paperLeastLambdaOHull is not proved.
- The Ind2/Ind3 enlarged images are on other carriers; see §11.

## 11. Ind2/Ind3 enlargement on the correct carrier (task-83 B)

Actual actions (source):
- ind2Act multiplies each coordinate by ζ ∈ rootsOfUnity (2l) in rootNormedExtension
  (Mzk1ThetaPilotObjectActual.lean:90-94); ind2Images :108-110.
- ind3Act multiplies each coordinate by an arbitrary u : (rootNormedExtension T b)^×
  (Mzk1ThetaPilotObjectActual.lean:98-101); ind3Images :113-115.
- On the L-valued carrier: ind2LValued/ind3LValued (PaperFinalLValuedTensorCarrierActual.lean:66-74);
  ind2Image/ind3Image/thetaImageIndUnion (PaperFinalLValuedThetaIndHullActual.lean:34-46).

Mathematical enlargement index analysis:
- Ind2: ζ is a root of x^{2l}-1, hence integral over the base and a unit of the integral
  structure O_L. Multiplication by ζ preserves the O_L-lattice O_L·x:
  O_L·(ζ x) = O_L·x. Therefore the generated lattice over the Ind2 orbit equals O_L·x;
  the finite index relative to O_L·x is 1. Ind2 gives no lattice-index gain.
- Ind3 as currently typed uses ALL nonzero field elements (rootNormedExtension)^×, not the
  integral units O_L^×. Its orbit of x≠0 is the whole K^× (take u=y/x), whose O_L-span is K.
  Hence there is no finite O_L-lattice index; the 'index' is infinite/undefined, not a
  positive finite enlargement. If Ind3 were restricted to O_L^×, it would again satisfy
  O_L·(u x)=O_L·x and give index 1.
- Carrier mismatch: even the finite index 1 is an index of lattices inside the root extension
  K=rootNormedExtension T b. The base qVFam block is the base completion/tensor block, not K.
  There is no constructed trace/norm/restriction map from K to the base block, so an index
  comparing the Ind orbit hull with F(c_root)*O_hol in the base block is undefined. A finite
  index expression depending only on l,p,different is therefore NOT available from the
  current objects.

Verdict on B:
- Ind2: no gain (index 1 on O_L-lattice); proof path: rootsOfUnity are integral units;
  multiplication by a unit preserves the fractional ideal/lattice.
- Ind3: no finite index as typed (all-field units give whole K); if corrected to integral
  units, no gain (index 1).
- Even in the integral-unit reading, the carrier comparison to the base block is missing;
  so no exact enlargement index of the form f(l,p,different) exists in the current tree.
- This is consistent with §4.8: the common-scalar part has no unbounded m-relative gain;
  Ind2/Ind3 on the correct carrier do not add a q-order-linear enlargement index.

Lean draft (not yet compiled; source-level objects):
- `ind2Orbit (x : rootNormedExtension T b) : Set K := {ζ*x | ζ ∈ rootsOfUnity (2l) K}`;
  `ind3Orbit (x) : Set K := {u*x | u : K^×}`.
- `ind3Orbit_eq_nonzero (hx : x≠0) : ind3Orbit x = {y | y≠0}` (elementary: u=y/x).
- For Ind2, `rootsOfUnity` integral/unit proof and `O_L·(ζx)=O_L·x` are the needed lemmas;
  no such packaged theorem is present, so the index-1 statement is source-level math, not
  a compiled theorem.
- A Lean `Mzk1Ind2EnlargementActual.lean` is not written in this task because the O_L-lattice
  API for rootNormedExtension and the division/trace bridge are not available; writing a
  file with only the orbit equality would not establish the index claim. No toy carrier used.

## 12. Original-text citations (exact)

| claim | file | line |
|---|---|---|
| F_l^⋇ = F_l^×/{±1}; l*=(l-1)/2 | papers/motizuki_corpus/text/Inter-universal Teichmuller Theory I.txt | 153-162 |
| j∈{0,...,l*}; |F_l|={0}∪F_l^⋇ | .../Inter-universal Teichmuller Theory II.txt | 125-130 |
| label 0 = mono-analytic core | .../Inter-universal Teichmuller Theory II.txt | 285-292 |
| theta values q^{j^2} depend on j∈F_l^⋇ | .../Inter-universal Teichmuller Theory III.txt | 4512-4519 |
| theta labels j∈F_l^⋇ elsewhere | .../Inter-universal Teichmuller Theory III.txt | 523-524, 1084, 1182 |
## 13. task-86 P0-fix / P4 status (read-only + build relay)

P0-fix file: tmp/sheaf/xif/paper/Mzk1PaperFaithfulHullActual.lean.
Current source (mtime 2026-11-12T20:24:57Z, 111 lines) defines:
- `paperFaithfulThetaImage := ⋃ j : PaperNonzeroLabel, thetaTensorScaledRegion (j^2 c_root)`
  using `qVFamPaperThetaTensorCoefficient` / `qVFamPaperRootCoefficient`;
- `paperFaithfulThetaHull := closure paperFaithfulThetaImage`;
- theorem `paperFaithfulThetaImage_eq_scaledRegion` (attempted equality to F(c_root)O_hol);
- theorem `paperFaithfulThetaHull_eq_closure_scaledRegion` (hull = closure scaled region);
- no use of the name `paperRootCoefficientFamily` in the current source.

Paper-faithful statement (target):
  paperFaithfulThetaHull = closure(F(c_root)·O_hol),  c_root = order(qVFamily)/(2l),
  over PaperNonzeroLabel only (S793:44/79); the old rootThetaHull includes j=0 and is not
  this object (task-83 §10).

Update (watchdog, 2026-11-12T20:30:43Z): `Mzk1PaperFaithfulHullActual.lean` is now GREEN:
DONE EXIT=0 (104s), olean 204400 bytes mtime 20:30:43Z; source 128 lines mtime 20:28:02Z.
Thus P0-fix definition + `paperFaithfulThetaImage_eq_scaledRegion` +
`paperFaithfulThetaHull_eq_closure_scaledRegion` are machine-checked. The P4 paper-hull
positive/finite statement remains the GAP below; only `ind3OutputHull_measure_pos_lt_top`
is green. The earlier stale-log note is superseded by this DONE line.

P4 status:
- existing green: `ind3OutputHull_measure_pos_lt_top`
  (rootNormHull_measure_pos + ind3OutputHull_measure_lt_top) is in the file; this gives
  0 < mu(ind3OutputHull) < top for any actual additive Haar mu.
- paperFaithfulThetaHull positive/finite is NOT yet proved in the current partial file;
  a proof needs `closure(F(c_root)O_hol)=F(c_root)O_hol` (compactness/closedness of the
  scaled region) or a direct subset of qPilotPaperRegion/rootNormHull.
  Exact missing pieces: closedness/compactness of `thetaTensorScaledRegion c_root`;
  identification of the paper-hull scaled region with `qPilotPaperRegion`; a trace/norm
  bridge is not needed for finiteness, but the closedness lemma is.

Build relay:
- `Mzk1Ind2EnlargementActual.lean`: watchdog DONE EXIT=0 at 2026-11-12T20:23:04Z (82s).
  This machine-checks the orbit definitions and `ind3Orbit_eq_nonzero` (all-field orbit);
  it does NOT prove Ind2/Ind3 lattice index (documented GAP).
- `Mzk1PaperFaithfulHullActual.lean`: watchdog DONE EXIT=0 at 2026-11-12T20:30:43Z (104s);
  olean 204400 bytes, source 128 lines (mtime 20:28:02Z). The earlier 20:23/20:26 errors
  were a stale revision; they are superseded by this DONE result.

## 14. task-86 conflict/notes

- Do not replace `paperFaithfulThetaImage` by the old rootThetaHull; the old one includes
  SignedLabel j=0 and is a model deviation.
- `PaperRootHullFormulaGap` must not be filled for the old hull; it is incompatible with the
  j=0 term unless R=F(c_root) (task-83 §10).
- P4 uses 0<mu<top before any toReal/log; the file only states the existing rootNormHull
  finite/positive facts for ind3OutputHull, not a new inequality.
## 15. P4-POS resolution (task-94/110): split file, positivity via S1023, finiteness via S920

Because the old P4 additions made the P0 file fragile, the delivery is split:
- `tmp/sheaf/xif/paper/Mzk1PaperFaithfulHullActual.lean` is restored to the P0-only
  green version (132 lines; old olean 204400 bytes).
- P4 is in **`tmp/sheaf/xif/paper/Mzk1PaperFaithfulHullP4Actual.lean`** (141 lines, 6434 bytes).

Build evidence (watchdog):
- `Mzk1PaperFaithfulHullP4Actual.lean` DONE EXIT=0 @2026-11-12T21:31:22Z (98s);
  olean 150512 bytes, mtime 21:31:22Z.
- source mtime 21:28:53Z.

Proved (machine-checked):
- `paperFaithfulThetaHull_eq_nonzeroHull`: paperFaithful hull = S806
  `paperRootThetaHullNonzero` (same PaperNonzeroLabel, same qVFamPaperThetaTensorCoefficient).
- `paperFaithfulThetaHull_measure_lt_top`: nonzero hull subset canonical unit reference
  (`s920PaperRegion_subset_O`), canonical is compact, `IsCompact.measure_lt_top`.
- `fractional_lattice_open`: F(paperRootCoefficientFamily) open via S1023
  `s923FractionalLatticeOpen_actual` (which uses S1022 local span-top and S1015 tensor openness).
- `fractional_subset_scaled`: F ⊆ F*O_hol via 1 ∈ O_hol.
- `scaledRegion_subset_paperHull`: F*O_hol ⊆ paperFaithful hull.
- `paperFaithfulThetaHull_measure_pos`: open F has positive Haar (IsOpen.measure_pos), measure_mono.

Therefore GAP-P4-POS is **resolved without the coefficient bridge**:
`qVFamPaperRootCoefficient = rootHalfCoefficient` / S1074NormCompatibilityOne / e=1 is NOT used.
The positivity uses the paper coefficient's own fractional lattice openness (S1023 actual), not qPilot.

Remaining caveat: S1023 depends on S1022 local span-top, whose proof is in the tree; no new
assumption was added. Finiteness depends on S920's paperNonzero hull containment; no equality
to qPilot/rootHalf is asserted.

## 16. task-94 / task-110 status

- task-94 (P4 finiteness): finiteness completed in the split P4 file; originally accepted as
  finiteness-only, now also positivity completed in the same P4 file.
- task-110 (P4-POS): closed by the independent S1023 openness route; no coefficient bridge used.
- task-115 remains: discharge S800 qPilotPaperRegionLog_le_paperHullLog pos/fin using the P4 file,
  and identify which hull S800's paperHullLog uses (rootThetaHull vs NonzeroHull) before mixing.