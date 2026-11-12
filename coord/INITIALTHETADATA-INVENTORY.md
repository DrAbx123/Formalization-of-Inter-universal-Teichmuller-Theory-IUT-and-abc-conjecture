# INITIALTHETADATA-INVENTORY — available constructions and gaps (A1030)

Status: read-only source inventory; no compile.

## 1. `Iut/Concrete/Existence.lean:303 thetaData`

Signature/inputs (lines 283-312):
- `C : EllipticCurveData.{u}`;
- `CA : C.CurveArithmetic`;
- `TI : C.TateInputs`;
- `{ℓ : ℕ}` with `hℓ : ℓ.Prime` **and `h7 : 7 ≤ ℓ`**;
- `R : C.ModEllRepData ℓ`;
- `hsl : ∀ A : SL(2,ℤ/ℓ), A.toGL ∈ R.rep.range`;
- `hP2 : ∀ w ∈ C.badAll, ¬ ℓ ∣ TI.qOrder w`;
- `hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ`;
- `hcore : OrbicurveDataSection.HasCoreUniversally C.F C.E`.

Produces:
`thetaData : InitialThetaData.{u}` with fields
`F := C.F`, `Fbar := C.Fbar`, `E := C.E`, `VBad := C.VBadOf ℓ`,
`global := C.globalData CA hP5`,
`prime := C.primeData CA TI hℓ h7 R hsl hP2`,
`orb := ...orbicurveData hcore`,
`localData := ...localThetaData ...`.

Consequences:
- `thetaData_qOrder` (:316): the constructed `qOrder` equals `TI.qOrder`;
- `logQ_eq` (:325): `qPilot.logQ = (C.localHeightData CA TI).heightOther 2 ℓ`.

**Important**: `h7 : 7 ≤ ℓ` excludes `ℓ = 5`; for l=5 this constructor is not
available as stated.  For ℓ ≥ 7 the full curve/Tate/modular-rep data are
required; none is present for a concrete model curve in the repo.

## 2. `SourceProcessionBoundary.Input` (`concreteInput l`)

`SourceProcessionBoundary.lean:33-50` fields:
- `theater : HodgeTheater`;
- `history : HodgeTheaterHistory`;
- `carrier : Carrier Label Choice`;
- `baseChoice`, `baseChoice_eq`;
- `packetVolume`, `packetVolume_eq_profile`, `base_packetVolume_eq_theta`;
- `target_q`, `target_q_eq`, `history_q_eq`;
- `route_normal_form`.

But this is **not** an `InitialThetaData`: it has no `F`, `Fbar`, `E`,
`VBad`, `global`, `prime`, `orb`, `localData`.  `concreteInput l`
(`:431-449`) supplies a Hodge theater/history/carrier with concrete labels
and Gaussian arithmetic, but **no elliptic curve, no field of moduli, no
admissible prime data**.  There is no field-by-field map to `InitialThetaData`;
converting it would require supplying exactly the missing curve/arithmetic/
modular data above.

## 3. S1487 data vs InitialThetaData

`S1487FaithfulInput : OriginalInput l S1487W` (`S1487...:537`) and
`S1487FaithfulC3 : SourcePilotRegionDataL` (`:548`) live at the
`OriginalInput`/L-carrier layer.  They provide:
- a `SourceDefinition31Data` over the concrete Gaussian arithmetic;
- a Hodge-theater family (shear model) and index equivalence;
- the S1391 L roots/Kummer/tensor fields;
- q candidate at the Gaussian five place.

They do **not** provide:
- `E : WeierstrassCurve F` with `IsElliptic`;
- `Fbar` algebraic closure / `IsAlgClosure`;
- `VBad : Set (FinitePlace (fieldOfModuli F E))`;
- `global : IsInitialThetaGlobalData`;
- `prime : AdmissiblePrimeData` (ℓ, torsion field, mod-ℓ representation);
- `orb : OrbicurveData`;
- `localData : LocalThetaData`;
so they cannot be packed as `InitialThetaData`.

## 4. What is needed for an `InitialThetaData`

| field/instance | needed data | present in repo? |
|---|---|---|
| `F`, `Fbar`, `Field`, `NumberField`, `Algebra`, `IsAlgClosure` | number field + chosen algebraic closure | no concrete curve field for S1487 |
| `E : WeierstrassCurve F`, `IsElliptic` | explicit elliptic curve | no |
| `VBad` | nonempty bad finite places of `fieldOfModuli F E` | no (S1487 badPlaces is a different type) |
| `global : IsInitialThetaGlobalData` | IUT I Def 3.1(a)-(b) global conditions | no |
| `prime : AdmissiblePrimeData` | admissible ℓ, ℓ-torsion field, mod-ℓ representation, coprimality | no |
| `orb : OrbicurveData` | orbicurve `C̲_K`, `X̲_K`, cusp ε | no |
| `localData : LocalThetaData` | valuation section `V`, local Θ-data | no |
| `h7 : 7 ≤ ℓ` (Existence constructor) | ℓ ≥ 7 | l=5 impossible via that theorem |

## 5. TG?

`InitialThetaData` (`Iut/Cor312/ThetaData/Basic.lean:81`) is built from
arithmetic/curve/orbicurve/local data; the `Existence.lean` constructor uses
`EllipticCurveData`, `CurveArithmetic`, `TateInputs`, `ModEllRepData`,
`OrbicurveDataSection`; **no `TemperedFundamentalGroups` import**.  TG is not the
blocker; the missing concrete curve/Tate/modular data and the ℓ≥7 restriction are.

## 6. Conclusion

- `thetaData` is the only concrete InitialThetaData constructor found; it needs
  full curve/Tate/modular-rep data and `ℓ ≥ 7`, so it does not produce l=5 and
  no such data exist concretely in the repo.
- `concreteInput l` is not convertible to InitialThetaData (different layer; no
  curve/field/modular fields).
- S1487 data are `OriginalInput`/L-carrier data, not InitialThetaData; the
  missing fields are the 8 listed above.
- lit/iv variant cannot be instantiated for S1487 without constructing an
  InitialThetaData (or a separate L-version RHSData).
