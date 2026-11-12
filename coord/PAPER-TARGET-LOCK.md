# PAPER TARGET LOCK (2026-10-24, user-approved)

用户决定：按 IUT 论文，而不是从更弱 native 输入构造 source。

## Locked target form

```lean
theorem paperP6
  (D : SourceDefinition31Data l)        -- 论文 initial Θ-data
  (hD : SourceConditions D) :           -- 论文合格条件
  PaperP6Conclusion D
```

不是：

```lean
theorem nativeP6
  (X : N8NativeInput l) :
  ∃ D : SourceDefinition31Data l, PaperP6Conclusion D
```

native 构造 source 是额外更强任务，不作为当前 target 义务。

## Allowed input (paper initial Θ-data)

- arithmetic/field data
- bad places partition
- reduction/torsion clauses
- orbicurve clause
- sections clause
- cusp clause
- paper-listed compatibility conditions

These may be fields of `D`/`hD`.

## Forbidden input (must be internal conclusions)

- q-pilot/Θ-pilot comparison
- local/global comparison morphism
- kappa=0 or S>=kappa
- h<=Theta or Q<=Theta
- ValuesBounded
- any effective zero divisor defined from the target inequality

## Current internal obligations

- O2: paper-faithful Θ^q/Θ^anab comparison; current volume-index formula false at index1.
- O3: actual local comparison divisor/effective zero; current natural lattice-index edge law false.
- O4: paper Θ/hull readout; current value-layer hull identity false/vacuous.
- O5: guarded Q<=Theta consumer; needs actual O3/O4.
- O6: paper P6/N8 conclusion.

## Current actual auxiliaries

- C9 counterexample/guard actual.
- qO/BPS/finite-observation actual.
- C6 partial actual: place fields, SourceAllowedOutput constructor, ellOut<=Theta under C6 facts.
- C7 LuSub<=LvSub/index actual.
- normalized completion isometry actual.

## Route

1. Reconstruct O2/O4/C7 formal objects from paper initial Θ-data, not current false value-layer definitions.
2. Use `SourceDefinition31Data` as qualified input; O1 native construction is not required.
3. Prove internal comparisons/Θ/guard.
4. Assemble paperP6 for qualified D.

## UPDATE after source semantics audit (2026-10-24)

- `SourceDefinition31Data` is a CONTRACT SHELL, not paper initial Θ-data. Audit: only arithmetic is actual object shape; places/reduction/torsion/orbicurve/sections/cusp/compat are bare types/arbitrary Props and can be degenerate.
- Cannot use `SourceDefinition31Data` as qualified paper input. Build new `PaperInitialThetaData` with actual Mathlib/production objects and actual source propositions; do not fill with True/PUnit/trivial-group/constant-Reals.
- Target form becomes `(D : PaperInitialThetaData l) -> SourceConditions D -> PaperP6Conclusion D`.
- O1/source construction is still not native-input construction; it is formalizing the paper's initial data fields with actual objects.

## Better source candidate: SourceInitialThetaData (2026-10-24)

- `SourceInitialThetaData` (IUTI/InitialTheta/SourceInitialThetaData.lean:3004) is a richer paper-shaped initial data structure: actual arithmetic/curve, Vmod/VbadMod actual places, clauses A-F, cusp/local data. Candidate paper input instead of shell `SourceDefinition31Data`.
- Task: audit whether `SourceInitialThetaData` is paper-faithful; if yes, construct `SourceDefinition31Data`/`OriginalInput` from it (actual projections, no arbitrary fill), then use as qualified input for theorem 3.11.
- Target form remains `(D : PaperInitialThetaData) -> PaperP6Conclusion D`, with PaperInitialThetaData = audited SourceInitialThetaData or its faithful refinement.
