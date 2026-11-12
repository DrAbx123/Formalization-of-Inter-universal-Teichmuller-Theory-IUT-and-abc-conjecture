# INITIALTHETADATA-CONCRETE-PATH — existing constructors and gaps (A1031)

Status: read-only source inventory; no compile.

## 1. Found concrete providers (Tripod)

`Iut/Tripod/CurveFacts.lean:369` `structure CurveProviders` fields:
- `torsionFinite3 : ∀ l : Qbar, TorsionFinite l 3`;
- `torsionFinite5 : ∀ l : Qbar, TorsionFinite l 5`;
- `arith : ∀ x : Pt, (curveOf x ...).CurveArithmetic`;
- `modRep : ∀ x ℓ, ℓ.Prime → (curveOf x ...).ModEllRepData ℓ`.

`Iut/Tripod/Providers.lean:34` gives a **closed term**:
`tripodProviders : CurveProviders`, constructed from
`legendre_torsionFinite`, `CurveArithmetic.ofCore`, `stable_reduction`,
`six_torsion_rational`, `galois_deg_prime`, `modEllRepData`.
(source closed; olean **absent** in current root build.)

From `P := tripodProviders` and `x : Pt` (`Iut.Tripod.Pt`):
- `C := P.curve x : EllipticCurveData` (`CurveFacts.lean:385`);
- `CA := P.arith x : C.CurveArithmetic` (`:375`);
- `TI := P.tate x : C.TateInputs` (`:389`);
- `R := P.modRep x ℓ hℓ : C.ModEllRepData ℓ` (`:377`);
- `localData := P.localData x` for the height/conductor side (`:392`).

## 2. Assembling `thetaData` from `tripodProviders`

`Iut/Concrete/Existence.lean:303 thetaData` needs:
`C`, `CA`, `TI`, `ℓ` prime with **`7 ≤ ℓ`**, `R`, `hsl`, `hP2`, `hP5`, `hcore`.

Available from Tripod:
- `C/CA/TI/R` as above;
- `hsl`: `Iut.Tripod.CurveFacts.sl2Image` (`:443`) proves
  `SL2ImageHyp P`, i.e. for every x, ℓ prime with `5 ≤ ℓ`,
  under `hP2`, `hP4` (no cyclic subgroup), `hP5`, the SL2 image condition;
- `hP2/hP5` are explicit hypotheses of `sl2Image`; they must be supplied;
- `hP4`: `¬ (P.curve x).HasCyclicSubgroup ℓ`; also a hypothesis;
- `hcore`: `OrbicurveDataSection.HasCoreUniversally C.F C.E`;
  `Iut.Tripod.coreFiniteness` (`Core.lean:98`) proves only *finiteness* of
  failures (exceptional j-invariants), so `hcore` remains an explicit input.

Thus a conditional assembly exists:
for `x : Pt`, `ℓ` prime `7 ≤ ℓ`, with `hP2`, `hP4`, `hP5`, `hcore`,
`thetaData` can be built from `tripodProviders`.  No ℓ=5 version: `h7 : 7 ≤ ℓ`.

## 3. Other input constructors

- `Iut/Concrete/TateInputsConstruct.lean:62 tateInputs : C.TateInputs`
  for arbitrary `C : EllipticCurveData` (uses `tateParameter` at bad places);
- `Iut/Concrete/CurveArithmeticProved.lean:239 CurveArithmetic.ofCore`
  for `C` with `IsSquare (-1)`, stable reduction, six-torsion rational,
  `F_λ/F_mod` Galois prime-to-ℓ;
- `Iut/Concrete/ModEllRepConstruct.lean:209 modEllRepData`
  for `C/ℓ` from a torsion basis;
- `Iut/Concrete/Existence.lean:242 globalData : IsInitialThetaGlobalData ...`
  for `C.VBadOf ℓ` (global condition constructed);
- `OrbicurveDataSection.HasCoreUniversally` has no universal instance;
  `coreFiniteness` only bounds exceptions.

No concrete `F/E` standalone instance was found besides the Tripod family;
`CurveProviders` is the only closed provider term, and its olean is absent.

## 4. Minimal concrete path

1. Take `P := tripodProviders` (`Iut/Tripod/Providers.lean:34`);
2. choose `x : Pt` (the Tripod point; any concrete point of the family);
3. choose a prime `ℓ ≥ 7` (e.g. ℓ=7), set `C := P.curve x`,
   `CA := P.arith x`, `TI := P.tate x`, `R := P.modRep x ℓ hℓ`;
4. supply `hP2 : ∀ w ∈ C.badAll, ¬ ℓ ∣ TI.qOrder w`,
   `hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ ≠ ℓ`,
   `hP4 : ¬ C.HasCyclicSubgroup ℓ`, and
   `hcore : OrbicurveDataSection.HasCoreUniversally C.F C.E`;
5. `hsl` from `Iut.Tripod.CurveFacts.sl2Image` (with `5 ≤ ℓ`);
6. `thetaData C CA TI hℓ h7 R hsl hP2 hP5 hcore`.

Missing/blocked:
- `tripodProviders` olean absent; its Tripod closure is large and not in the
  root build (needs script port/compile);
- `x : Pt`, `hP2`, `hP4`, `hP5`, `hcore` are not produced automatically;
- **ℓ = 5 is impossible** through this path because `thetaData` requires `7 ≤ ℓ`.
  l=5 needs a separate construction or a modified Existence theorem;
- no concrete `InitialThetaData` with ℓ=5 was found in the repo.

## 5. TG?

Tripod/Existence/CurveArithmetic/ModEllRep modules do not import
`TemperedFundamentalGroups`; the blocker is the missing Tripod closure olean
and the explicit hypotheses, not TG.

## 6. Conclusion

- A **conditional concrete path** exists: `tripodProviders` + point + ℓ≥7 +
  hP2/hP4/hP5/hcore, yielding `thetaData : InitialThetaData`.
- It does **not** give l=5 (h7).
- No unconditional concrete InitialThetaData instance exists in tree; l=5 remains
  the principal gap for our S1487/L target.
