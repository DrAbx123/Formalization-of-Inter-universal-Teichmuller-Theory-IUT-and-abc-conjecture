# C1 — Source input binding: SHEAF stage-1 record (revised)

任务 ID / 所属组 / owner / 日期：C1 / N8 closure / qside / 2026-10-22
目标节点 / SHEAF 阶段：C1 SourceInputBinding / stage 1 only.
文件：write `tmp/sheaf/n8/closure/C1-STAGE1.md`. No Lean file in this stage; no production edits.
集成负责人 / 构建负责人：C1 owner; C10 integrator later.
共享接口与冲突：C1 uses the same `I : OriginalInput l V` as C0.  It must NOT add fields to `OriginalInput`; place/realization bindings are a separate structure.  C2/C3/C4/C6 consume the resulting index.
续领范围：C1 stage2 `SourcePlaceRealization`/`SourceInputBinding`; C2/C3 stage1.

## 1. 数学目标（完整对象、量词、假设、结论）

```text
对每份 (l : PrimeGeFive, V : Type uv, I : OriginalInput l V)，
构造 C1 的源绑定 B(I)，其中：
  (a) 给出 V 与实际数域 F := I.initial.arithmetic.Fmod 的地方集合的等价；
  (b) C1 选出 v : V 以及实际 R : I.SourceImageRealization v；
  (c) 每个 I.primeStripAt n m 的每根纤维 Mon v 与对应实际局部值群有明确比较；
  (d) Hodge theater 族 arithmetic 对齐复用 I.arithmetic_alignment；
  (e) 生产化 Frobenioid 是独立子节点 C1-g1，不属于 SourceInputBinding 的自由字段；Prime/rho 比较若无类型则报告 gap。
```

C1 output is the shared source index for C2/C3/C4/C6, not a Theorem 3.11 output.  C1 does not construct packet/procession/vertical/evaluation/IPL/SHE/APT/hull/degree/q-output.

## 2. 原文与 route 位置

- coord/N8-CLOSURE-ROUTE.md §4 C1, §2 selection one, §3 S -> L/P/N.
- IUT III Example 3.6 (III p.107; corpus 6181–6548): global Frobenioids F⊛_MOD/F⊛_mod, local fractional ideals, comparison (iii).
- IUT III Proposition 3.7 (III pp.109–111): packet Frobenioids, F⊩-prime-strip.
- IUT I Examples 3.2/3.3/3.5, Cor 5.3: C_v, C⊢_v, C⊩mod, Prime(C⊩)~V, rho_v.
- Input boundary: IUT III Theorem 3.11 initial Theta-data + Hodge theaters only.

## 3. 允许输入 vs C1 必须产生

### 3.1 允许输入
1. `l : PrimeGeFive`, `V : Type uv`.
2. `I : OriginalInput.{u, uv, upi, umon, ui} l V`:
   - `initial : SourceDefinition31Data l`;
   - `family : SourceHodgeTheaterFamily l V`;
   - `index_equiv : family.index ≃ Int × Int`;
   - `arithmetic_alignment : ∀ i, (family.theater i).arithmetic = initial.arithmetic`.
3. The paper-given Hodge theater/link/lattice in `family`; C1 does not rebuild it.

### 3.2 C1 产生的精确结构（stage-2 候选，无 Lean now）

`SourcePlaceRealization I` exact fields:

```lean
structure SourcePlaceRealization (I : OriginalInput l V) where
  placeEquiv : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)
  -- NumberFieldPlaceIndex F = HeightOneSpectrum (𝓞 F) ⊕ NumberField.InfinitePlace F
  selected : V
  selected_realization : I.SourceImageRealization selected
  fiberMonEquiv : ∀ (n m : Int) (v : V),
    (I.primeStripAt n m).Mon v ≃*
      Multiplicative (placeLocalField (F := I.initial.arithmetic.Fmod) (placeEquiv v))
```

Here `v` and `R` are selected by C1, not input; `selected_realization` is produced by C1's source-image-realization child (C1-d), not by a free hypothesis.  `fiberMonEquiv` is an exact comparison field, not a free `Equiv` parameter of the theorem.

`SourceInputBinding I` exact fields (stage-2):

```lean
structure SourceInputBinding (I : OriginalInput l V) where
  place : SourcePlaceRealization I
```

The actual global Frobenioid is NOT a field.  It is a separate child obligation C1-g1 (production `SourceModelBackend`/`Carrier.frobenioidPresentation`); a `Nonempty` theorem must not fill an unconstrained Frobenioid datum.

The final stage-2 `fiberMonEquiv` uses the actual prime-strip value groups:

```lean
abbrev SourcePlaceValueGroup (F) [Field F] [NumberField F]
    (P : NumberFieldPlaceIndex (F := F)) : Type :=
  match P with
  | Sum.inl _ => finitePlaceValueGroup -- Multiplicative ℤ, Example36PrimeStripBridge.lean:164
  | Sum.inr _ => archimedeanValueGroup -- Multiplicative ℝ, Example36PrimeStripBridge.lean:483

fiberMonEquiv : ∀ (n m : Int) (v : V),
  (I.primeStripAt n m).Mon v ≃*
    SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (placeEquiv v)
```

The finite/infinite branches are the production donors `finitePlaceValueGroup`/`archimedeanValueGroup`, not newly invented groups.

### 3.3 严禁放入输入/严禁自由字段
- No arbitrary `placeEquiv`; the equivalence is a constructed obligation.
- No free `v`/`R` input: C1 selects them; C3 consumes them.
- No `Prime`/`rho_v` in input.
- No tmp `sourceOriginalInputFrobenioidPresentation` import; only production `SourceModelBackend`/`Carrier.frobenioidPresentation` or child C1-g1.
- No `SourceProposition37Frobenioid`/K2 `effective := True` or arbitrary `modMap/MODMap` as source comparison.
- No `Nonempty` total package.

## 4. 实际消费者

- C2: actual local field/completion/integer ring and principal units from `placeEquiv`, `placeLocalField`.
- C3: `I.primeStripAt` fiber value monoids via `fiberMonEquiv`; `selected : V` and `selected_realization : I.SourceImageRealization selected` feed `ThetaPilotPoint`/`sourceThetaPilotPoint`.
- C4: consumes C1's selected v and R to define witnessed output; v/R are not C4 inputs.
- C6: completion degrees/weights `[K_v:(F_mod)_v]` from `placeEquiv`/`placeLocalField`; no free weights.
- C10: same I index; C1 does not output Theorem 3.11.

## 5. statement_dependencies

| 依赖 | 文件:声明 | 状态 |
|---|---|---|
| `PrimeGeFive` | IUT 基础 | 已存在 |
| `SourceDefinition31Data` | LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:660 | 已存在 |
| `SourceHodgeTheaterFamily` | LeanFormal/IUT/IUTI/HodgeTheater/SourceHodgeTheaterFamily.lean:32 | 已存在 |
| `HodgeTheater` | LeanFormal/IUT/IUTI/HodgeTheater/HodgeTheaterCore.lean:31 | 已存在 |
| `OriginalInput` | LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean:41 | 已存在; unique input |
| `NumberFieldPlaceIndex` | LeanFormal/IUT/IUTII/Frobenioid/Example36PrimeStripComponentIdentification.lean:178 | 已存在 |
| `placeLocalField` | Example36PrimeStripComponentIdentification.lean:187 | 已存在 |
| `numberFieldPrimeStrip` | Example36PrimeStripComponentIdentification.lean:569-575 | 已存在 donor |
| `FPrimeStrip`/`FPrimeStripEquiv` | LeanFormal/IUT/IUTI/HodgeTheater/PrimeStripCore.lean:117-121,166-177 | 已存在 |
| `Iut.FrobenioidPresentation` | Iut/Foundations/Frobenioid.lean:915-916 | 已存在 |
| production backend | LeanFormal/IUT/IUTII/Frobenioid/Example36SourceModelBackend.lean + Iut/Foundations/SourceModelFrobenioidPresentation.lean:25-30 | 已存在 donor |
| tmp `sourceOriginalInputFrobenioidPresentation` | tmp/sheaf/n8/Group1Statement.lean:57-62 | NOT a dependency; candidate only |
| `SourceModelBackend.bottomBase_arrow_epi` | tmp group1 only | NOT production; child C1-g1 required |
| `SourceProposition37Frobenioid` | SourceDependencyChain.lean:995-1008 | reduced; not source comparison |

## 6. proof_dependencies

| 声明 | 状态 |
|---|---|
| `numberFieldPrimeStrip` / local value kernels | proved donor; not identified with `I.primeStripAt` |
| production `frobenioidPresentation` application at Fmod | **gap C1-g1** (production BottomBase connected/epi) |
| `SourcePlaceRealization.placeEquiv` | **gap C1-a** |
| `SourcePlaceRealization.fiberMonEquiv` | **gap C1-b** |
| `selected : V` / `selected_realization` | **gap C1-d** (C1 selects; C3 consumes) |
| strip/Frobenioid Prime/rho compatibility | **gap C1-c/G4**; no type |
| Hodge theater system/realization bridge | gap G9 |

## 7. 自然语言证明步骤

1. Take F := I.initial.arithmetic.Fmod; define `NumberFieldPlaceIndex F`.
2. Construct `placeEquiv : V ≃ NumberFieldPlaceIndex F` (finite height-one spectrum + infinite places); C1-a.
3. Select `v : V` from the source place data (requires C1-e nonempty/source selection; not free input).
4. Construct `R : I.SourceImageRealization v` from the actual q/theta value data; C1-d; C3 consumes it.
5. For each `n m v`, construct `fiberMonEquiv` from `numberFieldPrimeStrip` and the actual finite/infinite value groups `finitePlaceValueGroup`/`archimedeanValueGroup` (via `SourcePlaceValueGroup`); C1-b.
6. Construct global Frobenioid via production `Carrier.frobenioidPresentation` from `globalDivisorMonoidOn`/`numberFieldSourceModelInput`; needs C1-g1.
7. Prove `I.arithmetic_alignment` and the strip/Frobenioid compatibility; Prime/rho remains C1-c gap.

## 8. donors searched

Used/read: `SourceOriginalInput`, `SourceHodgeTheaterFamily`, `HodgeTheaterCore`, `PrimeStripCore`, `Example36PrimeStripComponentIdentification`, `Example36PrimeStripBridge`, `Example36SourceModelBackend`, `SourceModelFrobenioidPresentation`, `SourceInternalWiring`, `SourceImageHull`, `SourceDependencyChain`.

Not found:
- `V ≃ NumberFieldPlaceIndex Fmod`;
- `I.primeStripAt` fiber comparison;
- selected `v`/`R` construction;
- production `BottomBase` connected/epi and production global Frobenioid application;
- `Prime(C⊩)~V`, `dagger F⊢`, `rho_v` types;
- `SourceProposition37Frobenioid`/K2 source comparison.

## 9. exact gaps

- **C1-a**: `placeEquiv` not constructed; cannot add to `OriginalInput`.
- **C1-b**: `fiberMonEquiv` not constructed; final target is `(I.primeStripAt n m).Mon v ≃* SourcePlaceValueGroup (placeEquiv v)`, with finite branch `finitePlaceValueGroup = Multiplicative ℤ` and infinite branch `archimedeanValueGroup = Multiplicative ℝ` (Example36PrimeStripBridge.lean:164,483).
- **C1-d**: `selected : V` and `selected_realization : I.SourceImageRealization selected` not constructed; these are C1 outputs, not inputs.  `selected` needs a source nonempty/place selection (C1-e) not present in `OriginalInput`.
- **C1-g1**: productionization of group1 Frobenioid: `BottomBase` connected/epi and `frobenioidPresentation` application; tmp Group1Statement is not a production dependency.
- **C1-c/G4**: Frobenioid strip `Prime`/`rho_v`/`dagger F⊢` no type.
- G3/G5/G6/G7/G8/G9 from group1/route remain; C1 doesn't close them.
- `SourceInputBinding` has a `frobenioid_eq_production` field only after C1-g1; without it, no arbitrary `frobenioid` field may be added.

## 10. consumer C10 and acceptance

C10 consumes C1's same `I`, `selected v`, `R`, local place data and production Frobenioid.  C1 does not supply Theorem 3.11/IPL/SHE/APT/hull/degree/q output.

- stage1 deliverable: this record only.
- `statement_compiles`: not run/not applicable.
- `proof_body_checked`: not run/not applicable.
- `kernel_closed`/`target_accepted`: not run.
- stop boundary: after audit revise stage2 `SourcePlaceRealization`/`SourceInputBinding`; do not import tmp Group1Statement.
- next: reviewer audit; then child C1-g1 productionization and C1-a/b/d stage2 exact fields.
