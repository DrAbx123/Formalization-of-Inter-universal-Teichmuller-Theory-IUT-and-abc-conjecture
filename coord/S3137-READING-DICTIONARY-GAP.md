# S3137 reading-dictionary gap（只读核对）

## 结论
- 全树搜索 **没有** `PaperS3137ReadingDictionary`（`rg --hidden` 无结果）。
- 因此 q/P0 层的 correction 不能直接“接 S3137 字典”；必须先新建该字典或记录精确字段。

## 现有 S3137 读数定义
- `S3137QThetaPilotLogVolumeReadingsActual.lean:77-90`：
  `qPilotLogVolumeReading P = -|Real.log (‖P.line.C3.q.q‖)|`，且 `≤0`。
- 同文件 `:128-135`：
  `thetaPilotHullLogVolumeReal C3 = (haarLogVolume thetaPilotHullHaar thetaPilotHull).toReal`（raw Haar，不是 normalized hull）。
- `Mzk1ComparisonConditionActual.lean:43-44`：
  `qPilotLogVolumeReading P = Real.log ‖P.line.C3.q.q‖`（由 q norm<1/abs 变形）。

## 我们已有的 q 层（GREEN）
- `Mzk1P0QThetaReadoutNormCorrectionActual.paperQSignedReadout := -localLogMagnitude (qVFamily T b)`。
- `qhatLogReadout_sub_paperQ_eq_log_ratio`：`qhatLogReadout − paperQSignedReadout = log(qVFamNormRatio)`（norm agreement 下）。
- `paperQDegree_le_closedForm_sub_one_sub_correction` / `_of_fields`：degree 权重下 correction/conditional 形式。

## 精确缺口（S3137ReadingDictionary 需要的字段）
1. **q 对象识别**：
   `P.line.C3.q.q`（`SourcePilotRegionData` 空类型，S1429）与 `qVFamily T b` 不是同一实际对象；
   需要一个新的 actual `P`（或新的 actual q 参数）并证明
   `qPilotLogVolumeReading P = -localLogMagnitude (qVFamily T b)`；
   旧 C3 路径 vacuous，不能构造。
2. **theta 归一化**：
   `thetaPilotHullLogVolumeReal C3` 是 **raw Haar log-volume**；
   我们 signed theta 侧是 `s1915ClosedForm−1 = Σ d_b log r_b`（normalized product hull log）。
   两者之间需要 unit-mass normalization/isometry 字典：
   `rawLog(hull) = normalizedLog(hull) + log μ(unit)`；
   这不是 `s1915A0`（A0 是 clipped ENNMax），不能用。
3. **actual theta hull 对象**：
   `thetaPilotHull C3` 依赖 C3；若 C3 空，无法给出实际 hull measure，
   需要新的 actual theta hull 对象（root-extension product image hull）及 raw/normalized 关系。

## 建议
- 新建 `PaperS3137ReadingDictionary` structure，字段至少：
  `q_actual : ...`、`qread_eq : qPilotLogVolumeReading P = -localLogMagnitude q`、
  `theta_actual : ...`、`theta_raw_eq : thetaPilotHullLogVolumeReal C3 = rawHaarLog thetaHull`、
  `theta_normalized_eq : rawHaarLog thetaHull = (s1915ClosedForm−1) + log μ(unit)`；
- 再在该字典下组合我们的 correction/conditional form。
- 不修改 S3137 定义；旧 C3 空类型不能伪装成 actual 对象。
