# SourceUnitRegionHaarDataActual audit (Wave20)

Date 2026-10-24.  Target production file:

    LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean

## 1. Version before fix

- 523 lines, 22626 bytes
- SHA256 0d69c8753543efe3787b8412ccfdde0ad51a2bf7d82d1fa7c78682e35610323d
- compile: exit 1
- errors:
  - line 303: simpa fails on hprojHEq, "After simplification, term hprojHEq has type HEq ... but is expected to have type HEq ..." (printed types identical; dependent projection/instance transparency mismatch)
  - line 304: cases hprojHEq' fails with dependent elimination equation between the shear functions at i and j
  - line 306: congrFun hproj fails because hproj is equality of monoid homs, not plain functions
  - line 514: simpa with toAdd_ofAdd simplifies hto back to ofAdd minusOne = 1, while the goal is minusOne = 0 in the subtype
- warning line 115 (pre-existing): sourceHaarActualIntPairGroup class-valued def not marked reducible; non-blocking.

## 2. Diagnosis

The injectivity proof at 288-321 only needs the two shear coefficients n and m.
The original route went through HEq of proj () functions, then tried to
dependent-eliminate that HEq into an equality of monoid homs, then applied
congrFun.  The projection is dependent on the FPrimeStrip fields Pi/G, so:

- simpa cannot normalize the HEq type (303);
- cases cannot solve the function-equality motive (304);
- congrFun is the wrong eliminator for MonoidHom equality (306).

The only data needed is the value of the concrete shear on the two basis points.
Proving those two values directly avoids the dependent elimination.

The 514 error is a simp orientation issue: toAdd_ofAdd rewrites the hypothesis to
ofAdd minusOne = 1, but the goal after change is minusOne = 0 in the subtype.
Using congrArg toAdd, then change, then exact hto avoids the simp loop.

## 3. Minimal fix applied (proof terms only, no statement/definition changes)

At 295-318:

    have hprojHEq' : HEq (...) (...) := hprojHEq
    have hproj : ... := eq_of_heq hprojHEq'
    have h01 := DFunLike.congr_fun hproj (Multiplicative.ofAdd (0, 1))
    have h10 := DFunLike.congr_fun hproj (Multiplicative.ofAdd (1, 0))
    have hn : i.1 = j.1 := by
      have h01' : Multiplicative.ofAdd (shear i (0,1)) =
          Multiplicative.ofAdd (shear j (0,1)) := h01
      have h := congrArg (fun x => (Multiplicative.toAdd x).1) h01'
      simpa [sourceHaarActualShearAddEquiv] using h
    have hm : i.2 = j.2 := by
      have h10' : Multiplicative.ofAdd (shear i (1,0)) =
          Multiplicative.ofAdd (shear j (1,0)) := h10
      have h := congrArg (fun x => (Multiplicative.toAdd x).2) h10'
      simpa [sourceHaarActualShearAddEquiv] using h
    exact Prod.ext hn hm

At 507-510:

    have hEq : sourceHaarActualMinusOne = 0 := by
      have hto := congrArg Multiplicative.toAdd h
      change (sourceHaarActualMinusOne : sourceHaarActualNonpositiveAddSubmonoid) = 0 at hto
      exact hto

No definitions, statements, carriers, or value maps were changed.  This is a
proof-term repair only.

## 4. Version after fix

- 518 lines, 22486 bytes
- SHA256 7595add0d7d59b51ddccb0c4860889fd5dfdd678f00aa820c626e72d491404b4
- compile: exit 0
- remaining output: only the pre-existing line 115 linter warning.

Exact compile command:

    lake env lean -R D:/lean -j1 LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean

## 5. Impact

This was the R/sourceHaar actual-path blocker: the file could not be imported,
so sourceHaarActualOriginalInput, sourceHaarActualImageRealization and the
V=Unit/q=1 source image realization could not be consumed.

After this fix the production file is green (exit 0), so the actual R path is
importable.  Next consumer step: build the olean and use
sourceHaarActualImageRealization directly, rather than the independence-only
C1ActualImageRealizationAttempt path.

No other file was edited.  No target_accepted/kernel_closed/ABC claim.
