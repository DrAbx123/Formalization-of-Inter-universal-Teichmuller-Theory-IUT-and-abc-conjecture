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
