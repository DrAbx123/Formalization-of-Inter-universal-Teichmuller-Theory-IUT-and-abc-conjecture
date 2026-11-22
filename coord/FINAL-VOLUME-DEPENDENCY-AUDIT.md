# final/Volume 依赖检查（只读，2026-11-14）

## 文件
- `Mzk1P1PlaceVolumeFinal2Actual`
- `Mzk1P1PlaceVolumeSignFinalActual`

## 官方状态
- `Mzk1P1PlaceVolumeFinal2Actual`：GREEN 2026-11-13T17:40:18（olean 17:40）
- `Mzk1P1PlaceVolumeSignFinalActual`：GREEN 2026-11-13T17:43:26（olean 17:43）

## 依赖链
### Final2
imports：
- `Mzk1P1PlaceVolumeSignActual` — GREEN 18:58:25；
- `DeterminantLogVolumeActual` — olean 2026-10-28，无近期 FAIL；
- `Mzk1DetLinePlaceB5Actual` — GREEN 11:57:04；
- `Mzk1P1LocalGeneratorFromIsPrincipalActual` — GREEN 18:59:08；
- `Mzk1P1LocalizedFractionalIdealActual` — GREEN 18:48:03；
- `Mzk1Ob33B5AssemblyActual` — GREEN 18:59:11；
- **`Mzk1B5AssemblyNoHproductAttemptActual` — FAIL 2026-11-14T02:58:38**（olean 仍是旧 2026-11-13T15:21:02）。

### SignFinal
imports：
- `Mzk1P1PlaceVolumeSignActual` — GREEN 18:58:25；
- `DeterminantLogVolumeActual` — 旧 olean；
- `Mzk1DetLinePlaceB5Actual` — GREEN；
不依赖 `Mzk1B5AssemblyNoHproductAttemptActual`。

## 关键发现
1. **Final2 依赖的 `Mzk1B5AssemblyNoHproductAttemptActual` 当前 FAIL**（tail：`B5ProductFormulaBridge`/`qPilotDetArithmeticDegree_eq...`/`PaperOModuleActual.LocalField` unknown）。
   Final2 的 GREEN olean 是 17:40，早于该依赖变红；因此 Final2 **当前不可复现**，需要先修 B5 才能重新验证。
2. SignFinal 不依赖 B5，当前 olean 17:43 时其依赖（SignActual）当时已可编；SignFinal 相对稳定。
3. 两个 final/Volume 源中 grep `True`/`PUnit`/`sorry`/`axiom`：**无命中**。
4. Final2 本身只有 `placeVolumeFinal2Rows` 状态行（GREEN 声明），无新定理；它只是 re-export。SignFinal 有实际定理：
   - `placeLogVolume_nonneg_of_norm_le_one`
   - `placeLogVolume_nonpos_of_one_le_norm`

## 结论
- final/Volume 无 True/假目标；
- Final2 的 GREEN 依赖链已破（B5 red），不可当作当前可复现证明；
- SignFinal 独立且定理实际；
- 未改源。

## 时间戳确认（2026-11-14，本地 CST = UTC+8）

- `Mzk1B5AssemblyNoHproductAttemptActual.lean` source mtime：**11:19:24 CST**；
- `Mzk1P1PlaceVolumeFinal2Actual.olean`：**11:18:57 CST**（早于 B5 source 改动）；
- `Mzk1B5AssemblyNoHproductAttemptActual.olean`：仍是 **2026-11-13 23:21 CST** 的旧物；
- watchdog B5 最后记录：**11:18:36 CST FAIL**（也早于 source 11:19:24）。

因此：B5 在 Final2 编译之后又被修改，且旧 olean 一直是 11-13 23:21；Final2 当前 **不可复现**。
未改任何源。

## 更正（2026-11-14 11:40 CST）：B5 已绿，Final2 已重新编并可复现

- `Mzk1B5AssemblyNoHproductAttemptActual`：
  source mtime **11:23:30**；olean **11:26:33**；watchdog **11:26:34 DONE EXIT=0**；
- `Mzk1P1PlaceVolumeFinal2Actual`：
  source mtime **11:27:33**（晚于 B5 新 olean）；olean **11:29:42**；watchdog **11:29:42 DONE EXIT=0**。

因此先前“Final2 不可复现”已被后续官方编译解决：B5 先绿，Final2 在其新 olean 上重编绿。
未改源。
