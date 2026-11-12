# DECOMP-L-MODEL-SIGNS — signs and degeneracy in the L model (A993)

Status: symbolic/Lean-statement draft; **not compiled**.  Read-only result: the
source-set-volume L model is sign-degenerate under the realified producer — its
hull volume is `⊤`, so its log-volume is 0, not the paper R.

## 1. Definitions and their sign semantics

- `sourceLocalLogDegree v x = ∑ i : SourceVolumeIndex l, logDegreeAt 0 0 v (x i)`
  (`SourceImageHullVolume.lean:104`); a **real** number, sign free.
- `sourcePointVolume v x = ENNReal.ofReal (sourceLocalLogDegree v x)` (`:107`):
  **nonnegative ENNReal**; negative real log-degrees are truncated to 0 by `ofReal`.
  Hence it is not the signed local log-volume.
- `sourceSetVolume v S = ⨆ x∈S, sourcePointVolume v x` (`:188`):
  nonnegative ENNReal, monotone (`sourceSetVolume_mono`), may be `⊤`.
- `sourceHolomorphicHull v R n = holomorphicHull (sourceScalingUnits v)
  (possibleThetaPilotImageSet v R n)` (`SourceImageHull.lean:404`):
  a submonoid; no sign by itself.
- `sourceHullVolume v R n = sourceSetVolume v (sourceHolomorphicHull v R n)`
  (`:193`): nonnegative ENNReal, may be `⊤`.
- `logDegreeAt n m v x = Multiplicative.toAdd ((primeStripAt n m).degree v x)`
  (`SourceImageHull.lean:100`): real, sign free; with a realified value monoid the
  degree is the identity, so it is the real coordinate directly.

## 2. The degeneracy theorem

`SourceImageHullVolume.lean:428` proves, under **pointwise degree faithfulness**
  `hdeg : ∀ b, logDegreeAt 0 0 v (R.posRealAction (ofAdd b)) = b`,
that `sourceHullVolume v R n = ⊤` (the value-realized hull log-volume is infinite).
Our A986 producer `RealifiedValueMonoidAt.sourceImageRealization` satisfies exactly
this `hdeg` (`logDegreeAt_posRealAction`), for every `b`.

Consequently, for the A989 L chain:
- `thetaHullVolumeAtL hreal n v = ⊤` (draft theorem below);
- `globalThetaHullLogVolumeL hreal n = ∑ v, Real.log ((⊤ : ENNReal).toReal)
   = ∑ v, Real.log 0 = 0`,
  because `ENNReal.toReal_top = 0` and `Real.log 0 = 0`.

So the L model's `globalThetaHullLogVolumeL` is **0**, not R.  This is not a sign
error: `ENNReal.toReal` discards the infinite volume, and `log 0 = 0` masks it.
The source-set-volume model has no finite signed local volume; the negative `-A_v`
pieces (from q-scaling) are truncated by `ENNReal.ofReal` and then lost.

### Lean statement drafts (not compiled)

```lean
-- after opening the A989 file namespace and `hreal`
theorem thetaHullVolumeAtL_eq_top
    (n : ThetaPilotCarrier l) (v : S1487W) :
    thetaHullVolumeAtL (l := l) hreal n v = ⊤ := by
  unfold thetaHullVolumeAtL thetaHullVolumeAt
  exact sourceHullVolume_eq_top_of_degreeFaithful
    (I := S1487Input (l := l)) (R := S1487R (l := l) hreal v) n
    (fun b => (hreal v).logDegreeAt_posRealAction b)

theorem globalThetaHullLogVolumeL_eq_zero
    (n : ThetaPilotCarrier l) :
    globalThetaHullLogVolumeL (l := l) hreal n = 0 := by
  unfold globalThetaHullLogVolumeL globalThetaHullLogVolume
  simp [thetaHullVolumeAtL_eq_top, ENNReal.toReal_top, Real.log_zero]
```

These are **drafts**; mainline may compile/fix.

## 3. Per-term sign conclusions

| item | sign/status | reason |
|---|---|---|
| `sourcePointVolume` | ≥ 0 (ENNReal) | `ENNReal.ofReal` |
| `sourceSetVolume` | ≥ 0, possibly ⊤ | supremum of nonnegative |
| `sourceHolomorphicHull` | no sign | submonoid |
| `sourceLocalLogDegree` | sign free | finite sum of real log-degrees |
| `logDegreeAt` (realified) | sign free; identity degree | real coordinate |
| `thetaHullVolumeAtL` | `⊤` under A986 hdeg | `sourceHullVolume_eq_top_of_degreeFaithful` |
| `globalThetaHullLogVolumeL` | `0` | `toReal ⊤ =0`, `log 0=0` |
| negative `-A_v` pieces | LOST (not represented) | `ofReal` truncates negative degrees |

## 4. Consequence

- The L source-set-volume model is **not sign-faithful** for R: it cannot represent
  the negative q-scaling terms that make R positive; its hull volume is infinite
  and its log-volume collapses to 0.
- Therefore A989's `globalThetaHullLogVolumeL` is a **degenerate model value**, not
  R; the C line cannot use it to compute R or M=A−R.
- To repair, one needs either:
  1. the ambient `O`-module/hull log-volume with the paper's compactness/finiteness
     hypothesis (`SourceCompactBound` pattern), not `sourceSetVolume`; or
  2. a signed/real-valued local volume replacing `ENNReal.ofReal`-truncation
     (with the negative q-scaling kept), and an identification with `RHSData.vol`.

## 5. Next (draft)

- If mainline wants green: compile the two draft theorems only after the A989 file
  is green; they are immediate from `sourceHullVolume_eq_top_of_degreeFaithful`.
- Do NOT claim `globalThetaHullLogVolumeL = R`; the equality is false in this model
  (left side 0, right side paper R).
