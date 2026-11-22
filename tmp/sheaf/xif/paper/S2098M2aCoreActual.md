# S2098 — M2a-core of local reciprocity: actually inhabited

文件：`tmp/sheaf/xif/paper/S2098M2aCoreActual.lean`
- 行数：437
- SHA256：`2BAD79C191EAC76B12730D7FEC612DA0909C9A1962761DA10F33D64262A84520`
- 编译：`lake env lean tmp/sheaf/xif/paper/S2098M2aCoreActual.lean` → EXIT=0（日志 `S2098.out`）
- olean：`.lake/build/lib/lean/tmp/sheaf/xif/paper/S2098M2aCoreActual.olean`（468328 B，SHA256 `0C5131F2F98E2354C8D354C54265B0E292679BBB75FFE87E06165F42E2DB32FD`）
- axioms：19 个 `#print axioms` 探针全部仅 `propext / Classical.choice / Quot.sound`
- 禁止项：无 `sorry`/`admit`/`axiom` 声明（词法检查仅命中 docstring 文字）
- 消费者检查：`_S2098Consumer.lean` EXIT=0（导入 olean，instantiate S2027/S2024 结论）

## 结论

S2027 的 (M2a-core) 与 (M2a-torsion) 现在都有实际 inhabitant；`LocalArtinSourceData` 还差 exact field (M2c)，S2024 的 `LocalReciprocityData` 还差 (M2b)。

### 1. Artin retyped（无条件）

```lean
artinMaximalAbelian U : (localField p U)ˣ →* Gal(↥(maximalAbelianExtension p U) / localField p U)
artinMaximalAbelian_apply : 在有限 abelian M 上与 PadicField.abRec 一致
artinMaximalAbelian_eq_one_iff : ker = ⋂_{M : AbFin} normGroup M
```

### 2. localReciprocityIsomorphism（无条件 inhabitant）

来源：`PadicField.artinCompletionEquiv : Kˣ-hat ≃ₜ* Gal(K^ab/K)`
（`tmp/local-cft-port/Reciprocity/ProfiniteCompletion.lean`，证明消费局部存在定理
`PadicField.existence` 与 `PadicField.denseRange_artin`），沿 S2089 `galoisGroupEquiv` 运输：

```lean
unitProfiniteCompletionEquivGal U :
  unitProfiniteCompletion p U ≃* Gal(↥(maximalAbelianExtension p U) / localField p U)
unitProfiniteCompletionEquivGal_eta : (iso) (unitToCompletion U x) = artinMaximalAbelian U x
localReciprocityIsomorphism_holds U : localReciprocityIsomorphism p U
```

eta 方形说明这是 reciprocity iso，不是任意同构。

### 3. localArtinTorsion（无条件 inhabitant）

S2027 记为 missing 的 (M2a-torsion)，由 LANA 的
`PadicField.galAbEquiv : Gal(K^ab/K) ≃ₜ* 𝒪ˣ × Ẑ`（选 uniformizer）+ 三条本文件新证明的引理得到：

- `zhat_nsmul_eq_zero`：`Brauer.ZHat` 加法无挠（投影系统层级 `m*n → m` 论证）；
- `zhat_isOfFinOrder_eq_one`：`Multiplicative Zhat` 无非平凡挠；
- `torsionProdOfRightTorsionFree`：torsion 可分裂掉无挠因子；
- `nrm_coe_eq_one_of_isOfFinOrder`：单位根 `v = 0`（故 `nrm = 1`）；
- `torsionUnitGroupEquivMu`：`torsion 𝒪ˣ ≃* torsion Kˣ = mu(L)`。

```lean
galoisGroupMaximalAbelianEquivProd U : Gal(L^ab/L) ≃* (𝒪ˣ × Multiplicative Ẑ)
localArtinTorsionEquiv U : mu p U ≃* CommGroup.torsion (Gal(↥(maximalAbelianExtension p U)/L))
localArtinTorsion_holds U : localArtinTorsion p U
```

注意：S2027 记录的 “需要 Lˣ ≅ μ × pro-p × Z 的分解” 可用；本文件改用 Gal 侧分解
`Gal ≅ 𝒪ˣ × Ẑ`，因此不需要 Mathlib 的 unit structure theory。

### 4. LocalArtinSourceData / LocalReciprocityData：exact first missing

```lean
localArtinSourceArtin U : mu p U ≃* torsion (TopologicalAbelianization (localGaloisGroup p U))   -- 无条件
def localArtinSourceCarrierMissing : Prop := ∀ U, profiniteTorsionComparison p U                -- = (M2c)
localArtinSourceDataOfComparison (hc : localArtinSourceCarrierMissing) : LocalArtinSourceData p
def localReciprocityTransferCompatibility (hc) : Prop := <S2024 transfer_compat>                 -- = (M2b)
localReciprocityData_of_source (hc) (htransfer) : LocalReciprocityData p
localReciprocityOnTorsion_of_source (hc) : localReciprocityOnTorsion p
muQZComparison_of_source (hc) (htransfer) : muQZComparison p
muHatComparison_of_source (hc) (htransfer) : muHatComparison p
```

精确缺口（按依赖顺序）：
1. **(M2c)** `∀ U, Nonempty (torsion (Abelianization ↥U) ≃* torsion (TopologicalAbelianization (localGaloisGroup p U)))`。
   `abelianizationToTopological` 只有 surjective（S2027 已证）；torsion 上的单射无法从树中得到。
2. **(M2b)** 转移相容性（S2024 `transfer_compat`），即范数相容 `rec_H ∘ N = V ∘ rec_K`，树中没有。

两条都不假设、不伪造；`LocalArtinSourceData` 与 `LocalReciprocityData` 只作为条件构造给出。

## 依赖与构建

- 直接依赖：S2089FiniteAbelianSubextensionActual、S2027/S2024（经 S2089）、
  `Reciprocity.ProfiniteCompletion`、`Reciprocity.GaloisStructure`、
  `ClassFieldAxiom.HerbrandUnits`（`PadicField.unitGroup`，经 GaloisStructure 传递）。
- 构建：`Reciprocity.GaloisStructure` 原先缺 olean；本次
  `lake build Reciprocity.GaloisStructure` 重建 8717 jobs 成功。
  期间一次 `Reciprocity.ArtinContinuous` 在并发编译（探针同时运行）下
  `std::bad_alloc` 失败；单独重跑后成功（属资源问题，非源码/数学失败）。
- 本文件用 `lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2098M2aCoreActual.olean`
  产出 olean（`lake build tmp.sheaf...` 不是已注册 target）。

## Not run

全 Project 构建、target comparator、独立审查、[AbsTopIII] H^2 构造。(M2c)/(M2b) 只陈述未证明。
