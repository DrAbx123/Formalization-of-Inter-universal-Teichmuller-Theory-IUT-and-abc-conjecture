# S45 bypass via default-norm tensor constructor：类型层 obstruction（只读）

## 目标路线
用 default-completion generator q（default adic norm）直接构造
`ArithmeticTuplePureFractionalScalingData`，使 paper coefficient 由构造匹配，从而绕过 S45。

## 构造器实际类型
`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedUnitScalingLogVolume.lean:133-153`：
```lean
structure ArithmeticTuplePureFractionalScalingData (c : ι → ℝ) where
  localGenerator : (i : ι) → CommonPrimeCompletion (places i (tuple i))
  localGenerator_norm : ∀ i, ‖localGenerator i‖ = (p : ℝ) ^ (-(c i))
  ...
```
且唯一 unconditional constructor：
`FinitePlaceStepVAssembly.lean:112-115`：
```lean
def arithmeticTuplePureFractionalScalingData_ofGenerator
    (c : ι → ℝ)
    (g : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hg : ∀ i, ‖g i‖ = (p : ℝ) ^ (-(c i))) :
    ArithmeticTuplePureFractionalScalingData places tuple c
```

## 关键类型事实
- `CommonPrimeCompletion place := NormalizedCompletion place.val`（`FinitePlaceCommonPrimeCompletion.lean:20`）；
- 该类型上的 norm 是 **normalized spectral norm**（`QVFamNormalizedGeneratorSupplyActual` doc：
  "CommonPrimeCompletion ... norm is spectral"）；
- `qVFamDefaultNorm := ‖(qVFamily).q‖` 是 **default adic norm**（`QVFamNormalizedCoefficientBridgeActual:59`）；
- 两者是同一底层 type 的不同 norm instance，不能通过 `localGenerator_norm` 同时满足 paper coefficient。

## 直接尝试的障碍
若取 `g := qVFamily.q`（coerce 到 `CommonPrimeCompletion`）：
- `localGenerator_norm` 要求 `‖g‖_normalized = p^{-c}`，即 `c = c_norm`（normalized coefficient）；
- 不是 `paperNormalizedCoefficient`（default norm coefficient）；
- 若强行取 `c = paperCoeff`，则 `localGenerator_norm` 需要
  `‖q‖_normalized = p^{-paperCoeff}`，即 S45 ratio=1 / norm-instance equality。

## 结论
- 构造器 **只接受 CommonPrimeCompletion/normalized 实例**，不接受 default-norm generator；
- 因此不能用 default q 直接构造以绕过 S45；
- 这是 **类型/instance 层 obstruction**，不是缺证明；除非：
  1. 新增 default 版本的 scaling data structure；或
  2. 证明 norm-instance equality（S45）。
- 不 fake 构造器。

## 5. 更正/补充：default-norm variant 可构造（GREEN），但 downstream 不直接接受

### 已写并 GREEN
`Mzk1DefaultNormScalingVariantActual.lean`：
- `DefaultNormPureFractionalScalingData`：
  ```lean
  structure DefaultNormPureFractionalScalingData where
    localGenerator : (i : ι) → Completion (places i (tuple i)).val
    localGenerator_norm : ∀ i, ‖localGenerator i‖ = (p : ℝ) ^ (-(c i))
  ```
- `defaultNormPureFractionalScalingData_ofGenerator`：从 g/hg 构造；
- GREEN：**06:31:04（51s）**。

### 关键更正
- `CommonPrimeCompletion place := NormalizedCompletion place.val := Completion place.val`，
  因此 default 与 normalized 的 **底层类型是 defeq**；
- 所以 default generator 项可以 typecheck 到 `ArithmeticTuplePureFractionalScalingData.localGenerator` 的类型；
- 真正的障碍不是类型，而是 **norm instance proposition**：
  * default variant 的 `localGenerator_norm` 使用 default norm；
  * existing `ArithmeticTuplePureFractionalScalingData.localGenerator_norm` 使用 normalized/spectral norm；
  * 两个 proposition 不是 defeq；
- 因此不能把 `DefaultNormPureFractionalScalingData` 直接当 existing structure 用；
  需要 norm-instance bridge（S45 方向）或新增 default 版本 downstream。

### 结论（更新）
- default-norm structure + constructor **可行且已 GREEN**；
- 但 existing tensor constructor 仍只产生 normalized-norm scaling data；
- 要从 default supply 到 existing consumer，仍缺 `‖·‖_def = ‖·‖_norm` bridge；
- 这仍是 norm-instance obstruction，不是纯类型 no-go。
