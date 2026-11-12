# S2812/A — Does `S2717UpperGap` depend on `hdeg`?

Date: 2026-11-07
Audit result: **No.** `hdeg` is not a dependency of `S2717UpperGap`, and the
S2800 line-bundle bridge also does not use `hdeg`.  The hdeg blocker only
affects the S2600/S2601 source log-degree consumers.

## 1. S2717UpperGap is hdeg-free

File:

`tmp/sheaf/xif/paper/S2717Cor312FullTargetActual.lean`

The target is a plain `def : Prop`:

```lean
def S2717UpperGap
    (R : S1280RemainingClauses fiveLabel)
    ... (D : SourcePilotRegionDonors ...)
    (logQ dmod dFpd fFpd eStar etaPrm : Real) : Prop :=
  S2717ThetaHullLogVolume R ... D
    ≤ CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm *
      paperQAbsLog fiveLabel logQ
```

The two ingredients are:

```lean
noncomputable def S2717ThetaHullLogVolume ... : Real :=
  -((globalThetaHullInterface (C3 := ...)).logVolume
      (globalThetaHull (C3 := ...))).toReal

def S2717QPilotLogVolume ... : Real :=
  sourceQPilotSignedLog (...).initial
```

`globalThetaHullInterface` / `globalThetaHull` come from
`S2725GlobalThetaHullActual`; they are built from
`IQHullLogVolumeInterface` and `C3LogShellTensorBlock`, not from
`SourceImageRealization`.

Direct source audit:

```text
grep hdeg / SourceImageRealization / sourceHaarActual / ValueMonoidAt /
logDegreeAt in S2717Cor312FullTargetActual.lean
  => none
```

The same holds for the immediate dependency heads:

```text
S2717StageAMultiQActual
S2725GlobalThetaHullActual
S2711PaperMultiUnconditionalActual
S2715CThetaPaperScaleActual
S2691ExactQNormalizationActual
```

None mention `hdeg`, `SourceImageRealization`, `ValueMonoidAt`,
`sourceHaarActual`, or `logDegreeAt`.

The actual reduction theorem

```lean
theorem S2717_full_iff_hupper ... :
    PaperCor312Full ... ↔ S2717UpperGap ...
```

has axioms `[propext, Classical.choice, Quot.sound]` and no hdeg parameter.
Therefore **S2717UpperGap is independent of the S2810/S2812 blocker**.

## 2. S2800 line-bundle route is also hdeg-free

File:

`tmp/sheaf/xif/paper/S2800LineBundleCor312BridgeActual.lean`

```lean
structure S2800GlobalData (l : PrimeGeFive) where
  covolume : Set (S2800Carrier l) → Real
  W : IQHullLogVolumeInterface (S2800Carrier l)
  logShellPoint : Nat → Nat → Nat → S2800Carrier l

structure S2800EpsData (l) (G) (eps) where
  hregion : ...
  hheight : ...

noncomputable def S2800Bridge
    (G : S2800GlobalData l)
    (hg : ∀ eps : Real, 0 < eps → S2800EpsData l G eps) :
    Cor312ToABCBridgeInterface
```

No `SourceImageRealization`, no `ValueMonoidAt`, no `hdeg`.
The S2800 route replaces hdeg with:

```text
S2800GlobalData
+ hg : ∀ eps > 0, S2800EpsData (hregion + hheight)
```

The bridge code is actual (`S2800Bridge`, `S2800EpsilonComparison`, axioms
trio), but its inputs are not constructed.

## 3. What this does and does not bypass

### Bypasses hdeg

Yes. Neither route needs:

```lean
hdeg : ∀ b : ℝ,
  I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b
```

So the S2812 no-go does **not** block S2717UpperGap or the S2800 bridge
construction.

### Does not prove Cor 3.12 or ABC

`S2800Bridge` produces the frozen interface
`Cor312ToABCBridgeInterface`.  From
`LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean`:

```lean
theorem cor312ToABCBridge_abcConjecture
    (D : Cor312ToABCBridgeInterface) : ABCConjecture
```

and the file states the interface is inhabited iff `ABCConjecture` holds
(`cor312ToABCBridgeInterface_nonempty_iff_abcConjecture`).  Thus constructing
`G` and `hg` is at least as hard as the ABC content; the bridge is not a new
unconditional proof.  It is a conditional alternative route that avoids hdeg.

Likewise S2717UpperGap remains the single analytic target on the S2717 route;
S2800 does not prove it.

## 4. Practical priority

1. **Priority A result:** attack `S2717UpperGap` directly.  It is hdeg-free;
   the S2810/S2812 blocker is irrelevant to it.
2. For S2800, do not treat the bridge as a proof: it requires
   `S2800GlobalData` and an epsilon-family `hg`; these are at least ABC-hard.
3. Only S2600/S2601 source log-degree identities need hdeg.  If those consumers
   are not on the chosen route, do not build a new ValueMonoidAt carrier now.
4. If hdeg is later required, the S2812 result forces a new positive-degree
   value carrier / degree-splitting section; the existing source-Haar carrier is
   impossible.

## 5. Verdict

```text
S2717UpperGap depends on hdeg?          NO
S2800Bridge depends on hdeg?            NO
Can S2800 bypass source-Haar hdeg?      YES (conditional bridge)
Does S2800 prove Cor312/ABC?            NO; inputs equivalent to ABC content
Only S2600/S2601 need hdeg?             YES
```

No axiom, no fake action, no ABС assumption is introduced by this audit.
