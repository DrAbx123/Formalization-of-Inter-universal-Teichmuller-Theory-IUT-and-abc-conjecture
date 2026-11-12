# S2040 actual Θ-link and paper 3.12

Date: 2026-11-02. Status: Lean EXIT=0; actual Θ-link surface defined; paper 3.12 derived conditional on the paper link/comparison obligations. No reduced S1880/S1905/S1944 route is used.

## Lean file

`tmp/sheaf/xif/paper/S2040ActualThetaLinkActual.lean`

Names:

- `S2040ActualThetaLink left right O P`: two actual `HodgeTheater`s, an actual
  `HodgeTheaterLink left right`, actual q-pilot/O^x-mu compatibility props, and the
  paper log-volume/hull comparison field.
- `S2040ActualThetaLink.link_implies_inclusion`: the actual comparison implies
  `O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume`.
- `S2040ActualThetaLink.paper312_inequality`: `O.qPilotLogVolume ≤ P.signedHullLogVolume`.
- `S2040ActualThetaLinkObligations`: exact first-missing chain, no inhabitant.
- `S2040Paper312_of_obligations`: obligations produce the paper 3.12 inequality.

## Actual objects used

- `LeanFormal.IUT.HodgeTheater` and `HodgeTheaterLink` (actual prime-strip equivalence,
  theta q/scale equality).
- `PaperQPilotObject` (actual reduced source carrier with its four paper identification
  obligation fields).
- `PaperSignedHull` (actual signed hull/procession log-volume).
- `hullLogVolumeRay` / `mem_hullLogVolumeRay_iff` from the paper xi-f inclusion layer.

## Forbidden routes

Not imported and not used: S1880PaperO, S1905, S1944 reduced routes. No scalar
surrogate is named as the actual paper 3.12 proof.

## Exact first-missing chain

1. `O.paper_strip_identification`: actual q-pilot `(1,0)` F^boxplus-triangleright-x-mu prime-strip, not only the source F-layer strip.
2. `O.paper_lineBundle_identification`: actual rank-one arithmetic line bundle, not the reduced carrier.
3. `O.paper_logKummer_identification`: actual log-Kummer representation of q-pilot on `1,circ U_Q`, not the reduced `SourceKummerArrow`.
4. `O.paper_qPilot_log_identification`: actual procession-normalized q-pilot log-volume `-|log q|`.
5. `qPilotLogVolume_eq_paper` and `qPilotLogVolume_eq_neg_abs` with the actual q parameter.
6. Actual `qPilotLinkCompatibility` between the two Hodge theaters (q-pilot side).
7. Actual `omuLinkCompatibility` / O^x-mu link map between the two theaters.
8. Actual `logVolumeComparison` (paper holomorphic hull comparison), from which `link_implies_inclusion` and paper 3.12 follow.

No inhabitant of `S2040ActualThetaLinkObligations` or of the paper q-pilot object is asserted. The old `ThetaLinkActual` is a schema whose `link_implies_inclusion` is a field; S2040 separates the actual HodgeTheaterLink and makes the proof from comparison explicit.

## Axioms

`#print axioms` for `link_implies_inclusion`, `paper312_inequality`, and `S2040Paper312_of_obligations`: `[propext, Classical.choice, Quot.sound]` only. No `sorry`, `admit`, or custom axiom.

## S2030 cross-check (not a substitute)

S2030 (`tmp/sheaf/xif/paper/S2030Direct312Actual.lean`) gives an unconditional direct
3.12 inequality for any `T : SourceNativeInitialThetaData l`:

```
-|log S1487Cand.q| <= OrigXiFSignedThetaHullLogVolume (s2030D T h)
```

with no `[Fintype]` binder and no S1880/S1905/S1938/S1944 on its import cone; the
determinant is `s1940PaperLStarDeterminant` and the hull is `s1902ActualThetaHull`.
This is a genuine actual P-side/q-side scalar 3.12 route.

It does **not** supply the S2040 actual paper q-pilot object or the q-pilot/O^x-mu
Theta-link compatibility between two Hodge theaters: S2030 proves the numerical
inequality from the actual determinant average <= 1, without the paper Theta-link
object. Therefore S2030 is used here only as an obligation/consistency check, not
as a substitute for the S2040 actual O/Theta-link obligations, and it is not on the
S2040 proof path.

Consistency check to run once the actual O is constructed:

1. identify `O.qPilotLogVolume` with `-|log S1487Cand.q|` (the S1487 actual q);
2. identify `P.signedHullLogVolume` with
   `OrigXiFSignedThetaHullLogVolume (s2030D T h)` (or its `OrigXiFPaperSignedHull`);
3. then the S2040 `paper312_inequality` must coincide with S2030's unconditional
   inequality, so the actual-O route cannot produce a conflicting sign/normalization.


---

## Superseding milestone (2026-11-02, S2040ActualThetaLink312)

The report above records the earlier placeholder surface
tmp/sheaf/xif/paper/S2040ActualThetaLinkActual.lean.  That structure carries
logVolumeComparison (the conclusion) as a *field*, so its
link_implies_inclusion is a projection, not a derivation from actual link
data.  It is kept as history but is not the S2040 first milestone.

New artifact: tmp/sheaf/xif/paper/S2040ActualThetaLink312.lean

- 456 lines, 24673 bytes.
- SHA256 E53A19EE604CD91DF38E0879196AEB7E183714EBBEC7F6A5712538CDD9092F42.
- EXIT=0; log tmp/sheaf/xif/paper/S2040_build.log.
- Olean .lake/build/lib/lean/tmp/sheaf/xif/paper/S2040ActualThetaLink312.olean,
  1399856 bytes, SHA256 58EE6EA8203A25BAD86C2FEE06376B56DAE67AA9EC6A2822E878F5C8D26B28D1.
- Consumer tmp/sheaf/xif/paper/_S2040Consumer.lean, EXIT=0.
- Axioms: propext, Classical.choice, Quot.sound only (ten probes); no sorryAx.

What the new file adds over the placeholder:

1. Real scalar Theta-link q = Theta^(2l) with Theta = q^(1/(2l)):
   s2040Theta_pow, s2040Theta_log, s2040_log_q_eq_twoL_mul_log_theta,
   s2040_log_q_le_log_theta, s2040_signedLog_eq_log are proved
   unconditionally.
2. S2038PaperOActual: the exact S2038 interface (actual one-column q,
   actual (1,0)/(0,0) strips, the four paper q-pilot identifications).
3. S2040UnitsMuLink: the actual O^× -> O^×mu unit equivalence with
   CarriesRootSubgroup e mu nu.
4. S2040ThetaLinkDisplacement: the actual log-theta-lattice displacement data
   (root-stack Theta scalar, strips, unit link, ambient groups, integer and
   real degree maps, generators) and the actual
   ThetaLinkAssembly.thetaLink construction with thetaLink_generator and
   thetaLink_squaredLabelOrbit (generator and mu_(2l)-orbit compatibility).
   No inhabitant is asserted.
5. S2040ThetaLink312: the two actual Hodge theaters (0,0),(1,0) with their
   actual HodgeTheaterLink I.linkAt 0 0 1 0, the displacement, the q-pilot log
   identification, and the hull normalization.  link_implies_inclusion and
   paper312_inequality are theorems, not fields.
6. S2040FirstMissing: four exact components (paper O identifications, q-pilot
   log identification, actual displacement datum, paper hull normalization),
   with s2040ThetaLink312_of_firstMissing, s2040_inclusion_of_firstMissing,
   s2040_paper312_of_firstMissing, s2040FirstMissing_iff.

Remaining exact gaps: the actual root-stack Theta-pilot object (q[2u] on the
hodgeTwoLthRoot carrier, not the completion; S342 no-go), the actual O^× and
O^×mu groups/ambient values, the paper hull normalization
(P.signedHullLogVolume = log Theta; RootThetaHullNormalizationGap /
PaperRootHullFormulaGap), and the four paper O identifications.  No toy
instantiation and no inhabitant of the first-missing chain is asserted.

The S1880/S1905/S1944 reduced routes and the S2030 scalar direct route are
not imported and not used on this proof path.


## Root-stack Θ-pilot milestone (S2040RootStackThetaPilotActual)

The file `tmp/sheaf/xif/paper/S2040RootStackThetaPilotActual.lean` now constructs the
actual root-stack Θ-pilot object on the algebraic-closure root:

- `hodgeTwoLRootSystem`, `hodgeTwoLthRoot` (TwoLthRootKummerActual);
- `s2040RootStackThetaPilotObject` with `root_pow : root^(2l) = qVAlgClosedUnit`
  and actual `LGPThetaActionData`;
- `s2040Root_theta_value` identifies theta values with `lgpThetaValue`.

No completion root is used (S342 no-go).  The paper O^x/O^x-mu/ambient carrier is
recorded as the exact missing structure `S2040PaperOUnitsMuAmbient`: S1967 proves the
available source-strip unit group is unit-trivial and cannot be the paper local O^x.
The remaining obligations are packaged as
`S2040RootStackThetaPilotPaperObligations` (four q-pilot identifications, q-pilot/O^x-mu
compatibility, paper hull normalization, log-volume comparison); from it
`S2040Paper312OfRootStackObligations` derives the paper inequality.

### Root-stack build status

```
file:   tmp/sheaf/xif/paper/S2040RootStackThetaPilotActual.lean
EXIT=0; SHA256=B30EED5EEBBC7E80641007FA923C68FAD3BABD2F3F4D0CCDEBCE62BCFFBFB607
olean: yes; axioms: propext, Classical.choice, Quot.sound only
```

Paper hull normalization is not yet constructed; it remains in
`S2040RootStackThetaPilotPaperObligations.paperHullNormalization`, together with the
actual paper O^x/O^x-mu carriers and the four q-pilot identifications.

## Paper O^×/O^×μ carrier milestone

`tmp/sheaf/xif/paper/S2040PaperOUnitsMuAmbientActual.lean` uses the actual S1978
local O^×/O^×μ carrier (not the unit-trivial S1487 source-strip carrier) and the
actual S2032 local O^◃/q_v realification:

- `S2040LocalOUnitsCarrier 5` with actual local O^× and O^×μ, both proved nontrivial;
- `S2040LocalQVRealification D b` with the actual `q_v = 5 ^ order_b`, norm
  `paperQV D b`, and realified value `qPilotGeneratorValue D b`;
- `S2040CompletionLocalIdentification T b` is the exact missing identification of
  the Q_5 local model with the algebraic-closure completion units at `qVPlace T b`;
- `s2040PaperOUnitsMuAmbientOfCompletion` fills the paper O^×/O^×μ slot only after
  that completion identification is supplied.  No inhabitant of the completion
  identification is asserted.


## Canonical S2055/S2046 completion integral-units carrier

`tmp/sheaf/xif/paper/S2040CompletionBridgeS2055Actual.lean` uses the canonical
`S2055CompletionIntegralUnits` carrier and the canonical `S2046NormBridge`
(`S2055IntegralUnitsIdentificationRequired` plus `muCompatible`); it defines no
duplicate carrier.

- `s2040PaperOUnitsMuAmbientOfS2055 place` fills the paper O^×/O^×μ/ambient slots
  from S2055's actual completion integral units (not S2035 all-units).
- `S2040CompletionBridgeRequired T b` is exact missing: a rational
  `v : FinitePrimePlace 2 7`, the qVPlace completion ring bridge, the actual
  integral-units bridge to `S2055CompletionIntegralUnits (QPlace v)`, and the
  canonical `S2046NormBridge v`.  No inhabitant is asserted.
- `s2040PaperOUnitsMuAmbientOfBridge` consumes that bridge.

```
file:   tmp/sheaf/xif/paper/S2040CompletionBridgeS2055Actual.lean
EXIT=0; SHA256=D49BCC867D0A0D0823CF0058D6DB2D2989258AF78A14B20993FF0673FBCA0152
olean: yes
```

## Completion bridge layers (canonical S2055 / S2046)

`tmp/sheaf/xif/paper/S2040CompletionLayersActual.lean` splits the exact missing
`S2040CompletionBridgeRequired` into:

1. `S2040QVCompletionRingEquivRequired T b`: a rational v and
   `Completion (qVPlace T b) ≃+* Completion (QPlace v)`;
2. `S2040QVIntegralUnitsEquivRequired T b v`: the actual integral units
   `(Integers (AlgebraicClosure (Completion (qVPlace T b))))^×` identified with
   the canonical `S2055CompletionIntegralUnits (QPlace v)`;
3. `S2040QVNormBridgeRequired v`: the canonical `S2046NormBridge v`
   (`S2055IntegralUnitsIdentificationRequired` plus `muCompatible`).

`S2040CompletionBridgeOfLayers` assembles these into the bridge.  S2035's
`OUnitsActual = (Lv)^×` all-units carrier is not used; only S2055 integral units
are used for the paper O^× slot.  No inhabitant of the layers is asserted.

```
file:   tmp/sheaf/xif/paper/S2040CompletionLayersActual.lean
EXIT=0; SHA256=E838FDA52C3EE03EB4D99D48C7AA31AF53EA97C4E622F9F930E9F3E2E9507FAC
olean: yes
```

## S2056 isometry constructs layer (3); layers (1)+(2) remain missing

`tmp/sheaf/xif/paper/S2040NormBridgeS2056Actual.lean`:

- `s2040NormBridgeOfS2056Isometry v I` constructs the canonical `S2046NormBridge v`
  from an S2056 closure isometry `I : S2056ClosureIsometry (QPlace v)`, using
  `S2056IntegralUnitsEquiv` for the S2055 identification and `TimesMuQuotient.congr`
  for `muCompatible`.
- `S2040QVPlaceSplitData T b` is exact missing layer (1): a rational v, a
  norm-preserving ring equivalence `Completion(qVPlace T b) ≃+* Completion(QPlace v)`.
- `S2040QVIntegralUnitsBridgeRequired T b v` is exact missing layer (2).
- `s2040CompletionBridgeOfSplitAndS2056` assembles (1)+(2)+S2056 layer (3).

```
file:   tmp/sheaf/xif/paper/S2040NormBridgeS2056Actual.lean
EXIT=0; SHA256=C920197B0C2894F2716F0F18EEA28AEC530C7EB578A7A2437E9A29211B81468E
olean: yes
```

## qVPlace split/descent exact missing

`tmp/sheaf/xif/paper/S2040QVPlaceSplitActual.lean` records:

- `S2040qVPlace_eq_qVFamTensorPlace`: the actual qVPlace is `qVFamTensorPlace`;
- `S2040QVPlaceDegreeOneRequired T b := qVFamTensorRationalDegree T b = 1`;
- `S2040QVPlaceUnramifiedRequired T b := localRamificationIndex qVFamTensorPlace T b = 1`;
- `S2040QVPlaceSplitPackage T b`: a rational v, a norm-preserving ring equivalence
  `Completion(qVPlace T b) ≃+* Completion(QPlace v)`, and the two degree/unramified
  proofs;
- `S2040QVPlaceSplitDataOfPackage` turns the package into layer (1).

The source files do not supply degree one or unramifiedness; `BadPlaceRationalDegreeActual`
explicitly refuses to fake rationalDegree = 1.  Thus the exact first missing is the
source split/descent lemma `S2040QVPlaceDegreeOneRequired` together with
`S2040QVPlaceUnramifiedRequired` and the resulting norm-preserving completion ring
equivalence.  No inhabitant is asserted.

```
file:   tmp/sheaf/xif/paper/S2040QVPlaceSplitActual.lean
EXIT=0; SHA256=37A2B3FDC4293AF657AE0BAD1702629F191E37CFB963117F9AEDBB2DAB20EAF6
olean: yes
```

## S2060/S2065/S2057 corrections

- S2040CompletionLocalIdentification now uses the **integral** units
  `(Integers (SourceAlgebraicClosure (qVPlace T b)))^×`, not the all-units carrier.
  S2060 constructs the actual integral-units bridge and the actual
  `S2040PaperOUnitsMuAmbient`; `S2040S2060Actual` connects them.
- S2065 constructs the unconditional closure isometry and `S2065NormBridgeOf`, so
  layer (3) is no longer conditional.  S2040S2060Actual uses
  `s2040NormBridgeUnconditional v := S2065NormBridgeOf v`.
- S2057 constructs the actual finite root-stack Kummer groupoid and
  `S2057RootStackThetaPilotObject` (q[2u], thetaValue j = q[2u]^(j^2), norm/divisor
  laws, root = hodgeTwoLthRoot).  `S2040S2057InterfaceActual` records it.

**Correction:** `S2040RootStackThetaPilotActual.S2040RootStackThetaPilotObject` is
an algebraic-closure LGP model, not the paper finite root-stack O^tri(T_X) carrier.
It must not be used as the paper O^tri carrier.

**Exact missing paper root-stack data:** paper O^tri(T_X) carrier, its q_v, and
O^×μ attachment (S346 spec has no inhabitant; S342 no-go excludes the repo
qVFamily completion root).  See `S2040PaperOtriAttachmentRequired` in
`S2040S2057InterfaceActual`; no inhabitant asserted.

```
S2040S2060Actual.lean          EXIT=0 SHA256=60E0B08ECD0F332719925A89004FF428E4EC52A50876ECA6EB276723256C557A
S2040S2057InterfaceActual.lean EXIT=0 SHA256=325C0E3BF7FCD320F30CDEB10E860AD0DBDE75D89F928240AB386EEE07F9922B
```

## Latest layer status (S2057/S2060/S2065)

- Layer (2), corrected integral-units form: **actual** via S2060's
  `s2060CompletionLocalIdentification` / `s2060PaperOUnitsMuAmbient`, connected by
  `S2040S2060Actual.s2040CompletionLocalIdentificationActual` and
  `s2040PaperOUnitsMuAmbientActual`.  This uses `(Integers (SourceAlgebraicClosure
  (qVPlace T b)))^x`, not the all-units carrier.
- Layer (3): **unconditional** via S2065 `S2065NormBridgeOf`,
  `s2040NormBridgeUnconditional`.
- Layer (1): exact missing source split/descent data
  `S2040QVPlaceDegreeOneRequired`, `S2040QVPlaceUnramifiedRequired`, plus the
  norm-preserving `Completion(qVPlace T b) ≃+* Completion(QPlace v)`.
- Paper O^tri root-stack: S2057 actual finite root-stack groupoid/theta object;
  the earlier `S2040RootStackThetaPilotObject` is an algebraic-closure LGP model,
  not the paper O^tri carrier.  Paper O^tri/q_v/O^xmu attachment remains
  `S2040PaperOtriAttachmentRequired` (no inhabitant).

```
S2040PaperOUnitsMuAmbientActual.lean SHA256=6DBDBD2C88C7397266FC9EB07BB8564621D40414B8590ABC2360C34C678E24A8
S2040S2060Actual.lean               SHA256=60E0B08ECD0F332719925A89004FF428E4EC52A50876ECA6EB276723256C557A
S2040S2057InterfaceActual.lean      SHA256=325C0E3BF7FCD320F30CDEB10E860AD0DBDE75D89F928240AB386EEE07F9922B
S2040QVPlaceSplitActual.lean        SHA256=37A2B3FDC4293AF657AE0BAD1702629F191E37CFB963117F9AEDBB2DAB20EAF6
```

## Paper O^tri / q_v / O^×μ actual from S2092

`tmp/sheaf/xif/paper/S2040PaperOtriFromS2092Actual.lean` fills
`S2040PaperOtriAttachmentRequired` with S2092's actual paper carrier:

- `Otri := paperOtri T b` (nonzero integral elements at `sectionKPlace T b`);
- `qv := paperQV T b` (= `sectionQ T b`);
- `OUnits := paperOUnits T b` (integral units);
- `OUnitsMu := paperOUnitsMu T b` (2l-th roots of unity);
- `OUnitsMu_attachment` proved by `paperOUnitsMu_pow`;
- `norm_law` proved by `paperQV_norm_lt_one`;
- `qv_root_attachment := paperOtriRootMissing T b`, i.e. the completion
  `2l`-th root `q_v^{1/2l} ∈ O^tri_{K_v}`, exactly S1413's `SectionTwoLRoot`.

Thus the paper carrier/q_v/O^×μ parts are actual; only the completion root is
missing.  No qVFamily root, no all-units, no speculative orbifold carrier.

```
file:   tmp/sheaf/xif/paper/S2040PaperOtriFromS2092Actual.lean
EXIT=0; SHA256=E44F9E418E58AD734848298A1034ADB51916E97D695AEA1C4C55A5C603ACD62B
olean: yes
```

## O^×μ semantic correction (S2092 roots vs TimesMuQuotient)

Audit finding: S2092's `paperOUnitsMu = rootsOfUnity (2l) (Integers K_v)` is a
subgroup, **not** the paper O^×μ = units modulo all torsion.  The S2040 attachment
was corrected to use the actual quotient:

```lean
abbrev s2040PaperOUnitsMu : Type := TimesMuQuotient (paperOUnits T b)
noncomputable def s2040PaperOUnitsMuMap : paperOUnits T b →* s2040PaperOUnitsMu T b :=
  TimesMuQuotient.quotientMap
```

Proved actual quotient facts:

- `s2040PaperOUnitsMuMap_ker : ker = CommGroup.torsion (paperOUnits T b)`;
- `s2040PaperOUnitsMuMap_surjective`;
- `s2040PaperMu2L_mem_torsion`: the `2l` roots of unity lie in the torsion kernel;
- `s2040PaperMu2L_quotient_trivial`: they map to `1` in O^×μ;
- quotient is torsion-free (`TimesMuQuotient`).

Thus `rootsOfUnity(2l)` is recorded only as the root-indeterminacy subgroup, not
as O^×μ.  The S2060 local-model ambient already used `LocalOFieldUnitsMu`
(=`TimesMuQuotient`), so that side was semantically correct.

Exact missing Galois action:

```lean
structure S2040PaperOUnitsGaloisActionRequired (T b) where
  G : Type u
  [groupG : Group G]
  action : G →* MulAut (paperOUnits T b)
```

No inhabitant.  Given any such action, the descended quotient action and its
quotient-map compatibility are proved by `s2040PaperOUnitsMuActionOfGalois` and
`s2040PaperOUnitsMuActionOfGalois_quotientMap` via `TimesMuQuotient.action`.

```
file:   tmp/sheaf/xif/paper/S2040PaperOtriFromS2092Actual.lean
EXIT=0; SHA256=BCEA192D822BA0F1D3FEE0FC033695BFA6EB28C09D8089EECBF519EAECF9E22D
olean: yes
```

## S2146: actual local Galois action on paper O^×

`tmp/sheaf/xif/paper/S2146PaperOUnitsGaloisActionActual.lean` constructs the
actual local Galois group of the paper's K-place:

```lean
abbrev S2146PaperGaloisGroup : Type :=
  paperClosure T b ≃ₐ[paperKv T b] paperClosure T b
```

Since `paperOUnits = (Integers (paperKv T b))^×` lies in the fixed field
`paperKv T b`, the canonical action of this absolute Galois group on `paperOUnits`
is trivial:

```lean
noncomputable def s2146PaperOUnitsGaloisAction :
    S2146PaperGaloisGroup T b →* MulAut (paperOUnits T b)
```

and `s2146PaperOUnitsGaloisAction_apply` proves `σ • u = u`.  This is the actual
action for this carrier, not an arbitrary choice.

The datum `S2040PaperOUnitsGaloisActionRequired` is now inhabited:
`s2146PaperOUnitsGaloisActionRequired`.  The descended O^×μ action and its
quotient-map compatibility are `s2146PaperOUnitsMuGaloisAction` and
`s2146PaperOUnitsMuGaloisAction_quotientMap`.

Semantic boundary: if the paper's O^× is taken to be units of the integral closure
in F̄_v (with nontrivial Galois/cyclotomic action), then S2092's carrier is the
K_v-unit subgroup, and the nontrivial-action carrier remains a separate missing
datum; the present construction does not claim it.

```
file:   tmp/sheaf/xif/paper/S2146PaperOUnitsGaloisActionActual.lean
EXIT=0; SHA256=44D2DA7DBF293E292756E5002F90ECA91EB3D1C153C257A0F2368A72EF115A04
olean: yes
```

## S2147: integral-closure O^× carrier with genuine Galois action

`tmp/sheaf/xif/paper/S2147PaperIntegralClosureOUnitsActionActual.lean` distinguishes
the paper's integral-closure O^× from S2092's K_v-unit carrier:

- actual carrier `S2147PaperIntegralClosureOUnits T b :=
  (Integers (SourceAlgebraicClosure (sectionKPlace T b)))^×`;
- actual Galois group
  `S2147PaperIntegralClosureGaloisGroup T b :=
   SourceAlgebraicClosure (sectionKPlace T b) ≃ₐ[NormalizedCompletion ...]
     SourceAlgebraicClosure (sectionKPlace T b)`;
- norm preservation `s2147_integralClosure_norm_eq` for every Galois automorphism,
  via `spectralNorm_algHom_eq`;
- induced integral-subring equivalence `s2147IntegersRingEquiv` and integral-unit
  equivalence `s2147IntegralUnitsEquiv`;
- genuine action `s2147PaperIntegralClosureOUnitsGaloisAction` on the integral
  closure units, not the trivial action on K_v units.

Exact missing nontriviality witness:
`S2147IntegralClosureNontrivialActionRequired T b` states existence of σ and u with
σ • u ≠ u.  No witness is fabricated.

```
file:   tmp/sheaf/xif/paper/S2147PaperIntegralClosureOUnitsActionActual.lean
EXIT=0; SHA256=1CF772C64B7183C4D9EA3499D7095965E54CB4B21512C6506383560F0565F422
olean: yes
```

## S2163: reduction of integral-closure nontriviality to a cyclotomic witness

`tmp/sheaf/xif/paper/S2163IntegralClosureNontrivialActual.lean` records the exact
explicit data still needed for `S2147IntegralClosureNontrivialActionRequired`:

```lean
structure S2163CyclotomicNontrivialWitness (T b) where
  n : Nat
  hn : 0 < n
  ζ : S2147PaperIntegralClosure T b
  hζ : IsPrimitiveRoot ζ n
  σ : S2147PaperIntegralClosureGaloisGroup T b
  hσ : σ ζ ≠ ζ
```

From any witness it constructs the integral unit
`s2163WitnessUnit := Units.ofPowEqOne ⟨ζ, integrality⟩ n` and proves
`s2163WitnessUnit_moved : action σ unit ≠ unit`, hence
`s2163NontrivialAction_of_witness :
 S2147IntegralClosureNontrivialActionRequired T b`.

The exact missing datum is `S2163CyclotomicNontrivialWitnessRequired T b :=
Nonempty (S2163CyclotomicNontrivialWitness T b)`.  No ζ or σ is fabricated; the
construction identifies precisely the required root of unity and the Galois
automorphism moving it.

Actual auxiliary fact proved: `s2163_rootOfUnity_mem_integers` (every root of
unity in the normed algebraic closure is integral).

```
file:   tmp/sheaf/xif/paper/S2163IntegralClosureNontrivialActual.lean
EXIT=0; SHA256=2939FECBF12305EFC556B9F34B367BB0DFBFF1CB61C7D56B5378A997DBB1F5F6
olean: yes
```

## S2174: actual primitive roots of unity; missing Galois move

`tmp/sheaf/xif/paper/S2174CyclotomicWitnessActual.lean` constructs, for every
`n > 0`, an actual primitive n-th root of unity in the normed algebraic closure:

```lean
s2174PrimitiveRoot T b n hn : S2147PaperIntegralClosure T b
s2174PrimitiveRoot_spec : IsPrimitiveRoot (s2174PrimitiveRoot T b n hn) n
```

using `HasEnoughRootsOfUnity.exists_primitiveRoot` for the algebraic closure of
`NormalizedCompletion (sectionKPlace T b)`.

The exact missing datum is a local Galois automorphism moving this root:

```lean
structure S2174GaloisMovesRootRequired (n : Nat) (hn : 0 < n) where
  σ : S2147PaperIntegralClosureGaloisGroup T b
  hσ : σ (s2174PrimitiveRoot T b n hn) ≠ s2174PrimitiveRoot T b n hn
```

and `S2174GaloisMovesPrimitiveRootRequired T b` states existence of some `n` and
such a move.  No σ is fabricated.

Any such move yields a full S2163 cyclotomic witness:
`s2174CyclotomicWitnessOfGaloisMove`.

```
file:   tmp/sheaf/xif/paper/S2174CyclotomicWitnessActual.lean
EXIT=0; SHA256=5BEB78DB103A0063E1156E0021851C429685418D311974C9157E52B929EA430D
olean: yes
```

## S2184: exact API gap for the Galois move

`tmp/sheaf/xif/paper/S2184GaloisMoveActual.lean` records the precise API gap
between the actual primitive root of S2174 and a Galois move.

Actual equivalence:

```lean
theorem s2184_degree_iff_notInBase
    (hint : IsIntegral K (s2174PrimitiveRoot T b n hn)) :
    S2184PrimitiveRootDegreeRequired T b n hn ↔
      S2184PrimitiveRootNotInBaseRequired T b n hn :=
  minpoly.two_le_natDegree_iff hint
```

where

```lean
def S2184PrimitiveRootDegreeRequired : Prop :=
  2 ≤ (minpoly K (s2174PrimitiveRoot T b n hn)).natDegree
def S2184PrimitiveRootNotInBaseRequired : Prop :=
  s2174PrimitiveRoot T b n hn ∉ (algebraMap K (SourceAlgebraicClosure ...)).range
```

Exact missing structure:

```lean
structure S2184GaloisMoveAPIRequired (T b) where
  n : Nat
  hn : 0 < n
  notInBase : S2184PrimitiveRootNotInBaseRequired T b n hn
```

No σ or degree proof is fabricated.  The tree still lacks either
(a) a proof that the constructed primitive root is not in the base completion,
(b) a second root of its minimal polynomial, or (c) a transport of the S2046
cyclotomic character to `SourceAlgebraicClosure (sectionKPlace T b)`.

```
file:   tmp/sheaf/xif/paper/S2184GaloisMoveActual.lean
EXIT=0; SHA256=133D0BDED321A1B75288DF3056EA3212F2510C40347358985CB4E03692EE6236
olean: yes
```

## S2198: not-in-base implies an actual Galois move (infinite Galois correspondence)

`tmp/sheaf/xif/paper/S2198GaloisMoveWitnessActual.lean` proves that the
not-in-base statement for the S2174 primitive root directly produces an actual
local Galois automorphism moving it, without choosing a second root:

```lean
theorem s2198_exists_galois_move_of_notInBase
    (hnot : S2184PrimitiveRootNotInBaseRequired T b n hn) :
    ∃ σ : S2147PaperIntegralClosureGaloisGroup T b,
      σ (s2174PrimitiveRoot T b n hn) ≠ s2174PrimitiveRoot T b n hn
```

Proof: suppose every σ fixes ζ; then ζ lies in `fixedField ⊤ = ⊥`
(`InfiniteGalois.mem_bot_iff_fixed`, `fixedField_bot`), i.e. in the base
completion, contradicting `hnot`.

Exact missing is now only:

```lean
structure S2198NotInBaseRequired (T b) where
  n : Nat
  hn : 0 < n
  notInBase : S2184PrimitiveRootNotInBaseRequired T b n hn
```

No inhabitant asserted.  Given one,
`s2198GaloisMovesRootRequired` and
`s2198GaloisMovesPrimitiveRootRequired_of_notInBase` construct the actual σ and
inhabit the S2174 missing structure.

```
file:   tmp/sheaf/xif/paper/S2198GaloisMoveWitnessActual.lean
EXIT=0; SHA256=2A74F9262224D28E0182D848A69DD4ECF1A0CA3E5E3557E1E73AFF14DCBC5FF6
olean: yes
```

## S2202: not-in-base proved; integral-closure nontrivial Galois action ACTUAL

`tmp/sheaf/xif/paper/S2202NotInBaseActual.lean` closes the not-in-base gap.
Let `p = completionRationalPrime (sectionKPlace T b)` and
`D = [NormalizedCompletion : Q_p]`.  Choose `n = p^(D+1)`.

- `s2202_pow_mul_pred_gt : D < p^D * (p-1)` (arithmetic).
- `s2202_primitiveRoot_notInBase`: the constructed primitive `n`-th root is not
  in `NormalizedCompletion (sectionKPlace T b)`.  If it were, its cyclotomic
  minimal polynomial would have degree `p^D*(p-1) > D`, while
  `minpoly.natDegree_le` bounds it by `D`; contradiction.
- `s2202NotInBase : S2198NotInBaseRequired T b`.
- `s2202GaloisMovesPrimitiveRootRequired :
   S2174GaloisMovesPrimitiveRootRequired T b` (via S2198).
- `s2202NontrivialAction :
   S2147IntegralClosureNontrivialActionRequired T b` (via S2163/S2174 witness).
- `s2202CyclotomicWitnessExists :
   S2163CyclotomicNontrivialWitnessRequired T b`.

Thus the integral-closure O^× nontrivial Galois action is no longer conditional.

```
file:   tmp/sheaf/xif/paper/S2202NotInBaseActual.lean
EXIT=0; SHA256=F24BA8D050D91294060C6A12E50C0E51512B527E9D72C4F92557975F1D9E7E04
olean: yes
```

## S2219: paper O^×/O^×μ carrier choice

S2035's semantic audit states the paper local O^× is the unit group of
`Integers L_v` for `L_v = F̄_v`, not the `K_v`-unit group of S2092.  S2219 selects:

```lean
abbrev S2219PaperOUnits : Type := S2147PaperIntegralClosureOUnits T b
abbrev S2219PaperOUnitsMu : Type := TimesMuQuotient (S2219PaperOUnits T b)
```

Actual data proved:

- `s2219QuotientMap : S2219PaperOUnits →* S2219PaperOUnitsMu`
  (`TimesMuQuotient.quotientMap`);
- `s2219QuotientMap_ker : ker = CommGroup.torsion`;
- `s2219QuotientMap_surjective`;
- `s2219GaloisAction` is the S2147/S2202 actual integral-closure action;
- `s2219OUnitsMuAction` is its descended TimesMuQuotient action;
- `s2219OUnitsMuAction_quotientMap` proves quotient-map compatibility;
- `s2219NontrivialAction` proves the action is nontrivial (from S2202).

S2092's `paperOUnits = (Integers K_v)^×` is the fixed/base `K_v`-unit subgroup
with trivial Galois action, not the paper integral-closure O^×; S2092's roots of
unity are only the root indeterminacy subgroup, not O^×μ.

```
file:   tmp/sheaf/xif/paper/S2219PaperOUnitsCarrierActual.lean
EXIT=0; SHA256=924DEF48AE14EB376EB3AD103DC6DA98CB2E680CD16ED41198FBDF1FB5C3687F
olean: yes
```

## S2222: paper O^×μ attachment; q_v/logKummer exact missing

`tmp/sheaf/xif/paper/S2222PaperOUnitsMuAttachmentActual.lean` attaches the S2219
paper O^×/O^×μ carrier to the S2040 attachment semantics.

Actual `S2222PaperOUnitsMuAttachment`:

- quotient map `s2219QuotientMap` has kernel `CommGroup.torsion` and is
  surjective (S2219);
- the descended action on `S2219PaperOUnitsMu` is compatible with the quotient
  map (`s2219OUnitsMuAction_quotientMap`);
- the action is nontrivial (S2202).

Torsion/2l-root indeterminacy:

- `s2222_torsion_quotient_trivial`: any torsion unit maps to `1` in the paper
  O^×μ quotient;
- `s2222_pow_eq_one_quotient_trivial`: any unit with `u^n = 1`, `n > 0`, in
  particular a `2l`-th root of unity, maps to `1`.

Thus roots of unity are the indeterminacy kernel, not the O^×μ carrier; no
rootsOfUnity carrier is used.

Exact missing q_v/logKummer compatibility:

```lean
structure S2222QVLogKummerRequired (T b) where
  qv : S2147PaperIntegralClosure T b
  qv_integral : qv ∈ Integers (S2147PaperIntegralClosure T b)
  qv_norm_lt_one : ‖qv‖ < 1
  logKummer : S2219PaperOUnits T b →* S2219PaperOUnits T b
  logKummer_qv_compatible : Prop
```

No inhabitant asserted.  The missing point is the actual paper q_v in the
integral closure (not the S2092 K_v element) together with its log-Kummer action
on the selected paper units.

```
file:   tmp/sheaf/xif/paper/S2222PaperOUnitsMuAttachmentActual.lean
EXIT=0; SHA256=930C2972E9AE91A845BFEF276223633762799F27F78AC153373D17C79CDAB036
olean: yes
```

## S2230: actual q_v candidate in integral closure; logKummer exact missing

`tmp/sheaf/xif/paper/S2230QVLogKummerActual.lean` constructs the candidate

```lean
noncomputable def s2230qv : S2147PaperIntegralClosure T b :=
  algebraMap (NormalizedCompletion (sectionKPlace T b))
    (S2147PaperIntegralClosure T b)
    ((paperQV T b : paperOtri T b) : paperKv T b)
```

from the actual S2092 paper q_v.  The remaining properties are exactly missing:

```lean
structure S2230QVLogKummerRequired (T b) where
  qv_ne_zero : s2230qv T b ≠ 0
  qv_integral : s2230qv T b ∈ Integers (S2147PaperIntegralClosure T b)
  qv_norm_lt_one : ‖s2230qv T b‖ < 1
  logKummer : S2219PaperOUnits T b →* S2219PaperOUnits T b
  logKummer_qv_compatible : Prop
```

No inhabitant asserted.  Exact API gap: the original completion norm and the
normalized-completion norm are different instances, so the S2092 norm estimate
`paperQV_norm_lt_one` does not directly transport to the integral closure; and no
log-Kummer action on the S2219 paper units is constructed.

```
file:   tmp/sheaf/xif/paper/S2230QVLogKummerActual.lean
EXIT=0; SHA256=183FEC2412B1B940E22064D9AB522B5BBF8D86604654F1520098421444A985A2
olean: yes
```

## S2238: q_v norm comparison and properties in the integral closure

`tmp/sheaf/xif/paper/S2238QVNormActual.lean` uses
`normalizedCompletion_norm_lt_one_iff` to transport the S2092 q_v estimate from
the completion norm to the normalized spectral norm, then maps into S2147.

Actual result:

```lean
noncomputable def s2238x : NormalizedCompletion (sectionKPlace T b) :=
  (normalizedCompletionRingEquiv (sectionKPlace T b)).symm
    ((paperQV T b : paperOtri T b) : paperKv T b)

noncomputable def s2238qv : S2147PaperIntegralClosure T b :=
  algebraMap (NormalizedCompletion (sectionKPlace T b))
    (S2147PaperIntegralClosure T b) (s2238x T b)
```

Proved:

- `s2238x_norm_lt_one`;
- `s2238qv_norm_lt_one : ‖s2238qv‖ < 1`;
- `s2238qv_integral : s2238qv ∈ Integers (S2147PaperIntegralClosure T b)`;
- `s2238qv_ne_zero`.

Exact remaining logKummer datum:

```lean
structure S2238LogKummerRequired (T b) where
  logKummer : S2219PaperOUnits T b →* S2219PaperOUnits T b
  logKummer_qv_compatible : Prop
```

No inhabitant asserted.

```
file:   tmp/sheaf/xif/paper/S2238QVNormActual.lean
EXIT=0; SHA256=381E2DFB11C11744A44B4192EC50C2D3D253D13D47FBBC3241A2903C18C6CBD1
olean: yes
```

## S2245: log-Kummer exact first missing

`tmp/sheaf/xif/paper/S2245LogKummerActual.lean` records the exact log-Kummer
datum on the selected S2219 paper units:

```lean
structure S2245LogKummerRequired (T b) where
  logKummer : S2219PaperOUnits T b →* S2219PaperOUnits T b
  logKummer_qv_compatible : Prop
```

No inhabitant asserted.  API gap:

- the paper `logKummer` of `OrigXiFPaperLogKummerActual` is a
  `SourceKummerArrow G envStrip (sourceQPilotStrip boundary)`, not an
  endomorphism of the integral-closure unit group S2219;
- there is no canonical transport from that F-prime-strip arrow to
  `S2219PaperOUnits`;
- no p-adic logarithm is available on the non-complete algebraic closure
  `S2147PaperIntegralClosure` (the tree's `unitLog` APIs are for complete local
  fields), so a log on arbitrary integral-closure units cannot be fabricated.

`s2245ToS2238` proves the datum is exactly the S2238 logKummer obligation; it
The S2238 q_v properties themselves are actual.

```
file:   tmp/sheaf/xif/paper/S2245LogKummerActual.lean
EXIT=0; SHA256=6740A3C2EC8757FA8372B9F5337781CB8BFD673F1249A04C4CBB3233621AFABF
olean: yes
```

## S2249: SourceKummerArrow transport to paper O^×μ

`tmp/sheaf/xif/paper/S2249LogKummerTransportActual.lean` constructs the
canonical transport from a `SourceKummerArrow` to the selected paper O^×μ,
conditional on strip-unit-quotient identifications.

Exact missing identification:

```lean
structure S2249StripQuotientIdentificationRequired (T b) where
  V : Type uV
  upper lower : FPrimeStrip.{uMon, uV, uPi} V
  v : V
  G : Type uG
  [groupG : Group G]
  [topG : TopologicalSpace G]
  arrow : @SourceKummerArrow V G _ _ upper lower
  sourceIso : TimesMuQuotient ((upper.Mon v)ˣ) ≃* S2219PaperOUnitsMu T b
  targetIso : TimesMuQuotient ((lower.Mon v)ˣ) ≃* S2219PaperOUnitsMu T b
```

Given such data, the Kummer layer produces an actual automorphism:

```lean
noncomputable def s2249MuAut
    (D : S2249StripQuotientIdentificationRequired T b) :
    S2219PaperOUnitsMu T b ≃* S2219PaperOUnitsMu T b :=
  D.sourceIso.symm.trans ((D.arrow.layer.kummer D.v).equiv.trans D.targetIso)
```

Exact missing lift to an actual unit endomorphism:

```lean
structure S2249LogKummerOnUnitsRequired (T b) where
  muAut : S2219PaperOUnitsMu T b ≃* S2219PaperOUnitsMu T b
  unitMap : S2219PaperOUnits T b →* S2219PaperOUnits T b
  compat : ∀ u, s2219QuotientMap T b (unitMap u) = muAut (s2219QuotientMap T b u)
```

`s2249ToS2245` maps such data to the S2245 log-Kummer obligation.  No strip
identification or unit lift is fabricated.

```
file:   tmp/sheaf/xif/paper/S2249LogKummerTransportActual.lean
EXIT=0; SHA256=5963C087DEADAC989CD62C4583B43DDC4E4394B1D30C7216BB67D2A9FC22BD8E
olean: yes
```

## S2264: strip quotient identification via S2034

`tmp/sheaf/xif/paper/S2264StripQuotientIdActual.lean` uses S2034's actual

```lean
kummerMuEquiv v : actualOUnitsMu v ≃* TimesMuQuotient ((localOFieldStrip.Mon v)ˣ)
```

to build the source strip-quotient identification conditional on the exact
missing bridge from the S1978 completed local O^×μ carrier to S2219:

```lean
structure S2264ActualLocalBridgeRequired (T b) where
  v : LocV
  bridge : actualOUnitsMu v ≃* S2219PaperOUnitsMu T b

noncomputable def s2264LocalStripQuotientIso
    (B : S2264ActualLocalBridgeRequired T b) :
    TimesMuQuotient ((localOFieldStrip.Mon B.v)ˣ) ≃* S2219PaperOUnitsMu T b :=
  (kummerMuEquiv B.v).symm.trans B.bridge
```

Exact remaining q-pilot side:

```lean
structure S2264QPilotSideRequired (T b) where
  V : Type u
  upper : FPrimeStrip V
  lower : FPrimeStrip V
  v : V
  G : Type u
  [groupG : Group G]
  [topG : TopologicalSpace G]
  arrow : @SourceKummerArrow V G _ _ upper lower
  targetIso : TimesMuQuotient ((lower.Mon v)ˣ) ≃* S2219PaperOUnitsMu T b
```

No bridge, q-pilot arrow, or target identification is fabricated.

```
file:   tmp/sheaf/xif/paper/S2264StripQuotientIdActual.lean
EXIT=0; SHA256=5D6C60F7490C32C36F0CDAB7CEC3A3E491E038069539B1970C1962034CBA7BD1
olean: yes
```

## S2268: generalized closure isometry; local bridge conditional on paper-place prime

`tmp/sheaf/xif/paper/S2268LocalBridgeActual.lean` generalizes the S2065/S2056
closure isometry to the paper K-place:

```lean
s2268ClosureEquiv :
  SourceAlgebraicClosure (sectionKPlace T b) ≃ₐ[PadicScalarField ...]
    AlgebraicClosure (PadicScalarField ...)
s2268ClosureEquiv_norm : ‖s2268ClosureEquiv x‖ = ‖x‖
```

It induces actual integral-unit and O^×μ equivalences:

```lean
s2268IntegersEquiv :
  Integers (SourceAlgebraicClosure (sectionKPlace T b)) ≃+*
    Integers (AlgebraicClosure (PadicScalarField ...))
s2268IntegralUnitsEquiv :
  S2219PaperOUnits T b ≃* LocalOFieldUnits (s2268p T b)
s2268MuEquiv :
  S2219PaperOUnitsMu T b ≃* TimesMuQuotient (LocalOFieldUnits (s2268p T b))
```

For an explicit paper place `v : LocV` with `v.1 = s2268p T b`:

```lean
s2268LocalBridge v hv :
  actualOUnitsMu v ≃* S2219PaperOUnitsMu T b
s2268S2264BridgeOfPlace v hv :
  S2264ActualLocalBridgeRequired T b
```

Exact remaining missing: `S2268PaperVPrimeMatchRequired T b :=
∃ v : LocV, v.1 = s2268p T b` (a paper V-prime matching the contracted prime
of `sectionKPlace T b`).  No such place is fabricated.

```
file:   tmp/sheaf/xif/paper/S2268LocalBridgeActual.lean
EXIT=0; SHA256=4FD797DE952F073F587E42C1DB6EA9BC4CAC9DD6B70C83FC1D2A4D0633C2E833
olean: yes
```

## S2280: paper V-prime matching reduced to the known strip-alignment input

`tmp/sheaf/xif/paper/S2280PaperVPrimeMatchActual.lean` proves

```lean
theorem s2280_sectionKPlace_prime_eq_qVFamTensorP :
  s2268p T b = qVFamTensorP T b
```

via `completionRationalPrime = residueCharacteristic`, the contractions
`sectionKPlace -> sectionFPlace -> b.1`, and S2232's residue-characteristic
identification.

Hence `S2268PaperVPrimeMatchRequired` is equivalent to the already isolated exact
missing input

```lean
abbrev S2280QVFamPrimeStripRequired : Prop :=
  S2135PrimeAlignmentRequired T b
def S2135PrimeAlignmentRequired : Prop :=
  qVFamTensorP T b ∈ primeStrip 2 7
```

and strip alignment constructs the place and closes the S2264 bridge:

```lean
theorem s2280PaperVPrimeMatch_of_strip
    (h : S2135PrimeAlignmentRequired T b) :
    S2268PaperVPrimeMatchRequired T b

noncomputable def s2280S2264BridgeOfStrip
    (h : S2135PrimeAlignmentRequired T b) :
    S2264ActualLocalBridgeRequired T b
```

No strip-membership proof is fabricated.  S2232 records that this
`qVFamTensorP T b ∈ primeStrip 2 7` is the known source-side exact missing input
(for the concrete S1730 bad set it is available; not for arbitrary T).

```
file:   tmp/sheaf/xif/paper/S2280PaperVPrimeMatchActual.lean
EXIT=0; SHA256=7922043ADC736E0B2A5DDE3413A8126980808A38F37D60E0B1B9B870D41F76DA
olean: yes
```

## S2286: strip chain under S2135

`tmp/sheaf/xif/paper/S2286StripChainActual.lean` combines S2280 and S2264 with
the S2034 actual local Kummer arrow.  Under `S2135PrimeAlignmentRequired`:

```lean
noncomputable def s2286StripQuotientIdentification
    (h : S2135PrimeAlignmentRequired T b) :
    S2249StripQuotientIdentificationRequired T b
```

using `upper = lower = localOFieldStrip`, `G = LocG`,
`arrow = actualKummerArrow`, and the S2264 local strip quotient isomorphisms.

Consequently it yields the actual O^×μ automorphism

```lean
noncomputable def s2286MuAut
    (h : S2135PrimeAlignmentRequired T b) :
    S2219PaperOUnitsMu T b ≃* S2219PaperOUnitsMu T b :=
  s2249MuAut T b (s2286StripQuotientIdentification T b h)
```

Exact remaining data:

```lean
structure S2286RemainingRequired (T b) where
  primeAlignment : S2135PrimeAlignmentRequired T b
  logKummerUnits : S2249LogKummerOnUnitsRequired T b
```

No strip membership is fabricated.  This reduces the S2249 transport to exactly
the known S2135 arithmetic input and the unit-level log-Kummer lift.

```
file:   tmp/sheaf/xif/paper/S2286StripChainActual.lean
EXIT=0; SHA256=E58EDF93C49AC89CB5206206B280CF912380FCBC4E5A1D758CFE2AC77486CAEE
olean: yes
```

## S2288: unit log-Kummer lift and quotient-section gap

`tmp/sheaf/xif/paper/S2288UnitLiftActual.lean` reduces the S2249 unit lift to a
multiplicative section of the torsion quotient:

```lean
structure S2288QuotientSectionRequired (T b) where
  toUnit : S2219PaperOUnitsMu T b → S2219PaperOUnits T b
  toUnit_quotient : ∀ x, s2219QuotientMap T b (toUnit x) = x
  toUnit_one : toUnit 1 = 1
  toUnit_mul : ∀ x y, toUnit (x * y) = toUnit x * toUnit y
```

No inhabitant is asserted.  Given such a section and a quotient automorphism,
the actual unit endomorphism is constructed:

```lean
s2288UnitMapOfSection S f : S2219PaperOUnits T b →* S2219PaperOUnits T b
s2288UnitMapOfSection_quotientMap S f u :
  quotientMap (s2288UnitMapOfSection S f u) = f (quotientMap u)
s2288LogKummerOnUnitsOfSection S f : S2249LogKummerOnUnitsRequired T b
```

Combining with S2286's conditional quotient automorphism:

```lean
s2288LogKummerOnUnitsOfStripAndSection
    (h : S2135PrimeAlignmentRequired T b)
    (S : S2288QuotientSectionRequired T b) :
    S2249LogKummerOnUnitsRequired T b
```

Remaining exact data:

```lean
structure S2288RemainingRequired (T b) where
  primeAlignment : S2135PrimeAlignmentRequired T b
  quotientSection : S2288QuotientSectionRequired T b
```

No section is fabricated.  This isolates the unit-lift gap to the absence of a
multiplicative section of the torsion quotient.

```
file:   tmp/sheaf/xif/paper/S2288UnitLiftActual.lean
EXIT=0; SHA256=2E7CEA14D761EADEE262FB2CDEB06B0D065C574120C82D16673B665BE66EE218
olean: yes
```

## S2297: quotient section from a torsion retraction

`tmp/sheaf/xif/paper/S2297QuotientSectionActual.lean` proves that a multiplicative
retraction onto the torsion subgroup yields the S2288 quotient section.

```lean
structure S2297TorsionRetractionRequired (T b) where
  retraction : S2219PaperOUnits T b →* CommGroup.torsion (S2219PaperOUnits T b)
  retraction_torsion : ∀ t, retraction t = t
```

No inhabitant asserted.  Given `R`, the projection
`s2297Proj R u := u * (R.retraction u)⁻¹` is multiplicative, has the same
quotient class as `u`, kills torsion, and is independent of the representative:

```lean
s2297Proj_quotient
s2297Proj_mul
s2297Proj_torsion
s2297Proj_eq_of_quotient_eq
s2297Section R : S2288QuotientSectionRequired T b
```

The constructed section uses `Classical.choose` of quotient surjectivity only
for a representative; multiplicativity is proved from the retraction, not assumed.

Composing with S2286/S2288:

```lean
s2297LogKummerOnUnitsOfStripAndRetraction
    (h : S2135PrimeAlignmentRequired T b)
    (R : S2297TorsionRetractionRequired T b) :
    S2249LogKummerOnUnitsRequired T b
```

Remaining exact data:

```lean
structure S2297RemainingRequired (T b) where
  primeAlignment : S2135PrimeAlignmentRequired T b
  torsionRetraction : S2297TorsionRetractionRequired T b
```

No retraction or splitting of the torsion extension is fabricated.

```
file:   tmp/sheaf/xif/paper/S2297QuotientSectionActual.lean
EXIT=0; SHA256=07925DF994B69E5C7F630D784F34771773D2BD48C6C1ECDD72587433000D2B79
olean: yes
```

## S2302: torsion retraction ACTUAL; section and unit lift no longer conditional

`tmp/sheaf/xif/paper/S2302TorsionRetractionActual.lean` constructs the S2297
torsion retraction unconditionally.

1. Roots in the torsion subgroup:

```lean
theorem s2302_exists_root (n : Nat) (hn : 0 < n) (t : torsion U) :
  ∃ s : torsion U, (s : U) ^ n = (t : U)
```

Every root of unity has an n-th root in the algebraically closed field; the root
has norm one, hence is an integral unit, and is torsion because a power of it is
the original root of unity.

2. Divisibility of `Additive (torsion U)`:

```lean
instance s2302Rootable : RootableBy (torsion U) Nat
instance s2302DivisibleNat : DivisibleBy (Additive (torsion U)) Nat
instance s2302DivisibleInt : DivisibleBy (Additive (torsion U)) Int
```

3. Injection splitting via Baer/injective module:

```lean
noncomputable def s2302TorsionRetraction :
  S2297TorsionRetractionRequired T b
```

The inclusion of the divisible torsion subgroup into the units splits by
`Module.Baer.extension_property_addMonoidHom`.

Consequences:

```lean
noncomputable def s2302QuotientSection :
  S2288QuotientSectionRequired T b

noncomputable def s2302LogKummerOnUnitsOfStrip
    (h : S2135PrimeAlignmentRequired T b) :
    S2249LogKummerOnUnitsRequired T b
```

Hence the unit log-Kummer lift is now actual conditionally only on S2135.
The remaining datum is exactly:

```lean
structure S2302RemainingRequired (T b) where
  primeAlignment : S2135PrimeAlignmentRequired T b
```

No retraction, section, or S2135 is fabricated.

```
file:   tmp/sheaf/xif/paper/S2302TorsionRetractionActual.lean
EXIT=0; SHA256=03C859DBE18A4AE683AEFFB9D0255C616D0416A09BF71CDC2C34056B11CC8593
olean: yes
```

## S2321: final conditional paper O^×μ chain

`tmp/sheaf/xif/paper/S2321OUnitsChainFinalActual.lean` assembles the whole chain:

```lean
structure S2321OUnitsChain (T b) where
  primeAlignment : S2135PrimeAlignmentRequired T b
  stripIdentification : S2249StripQuotientIdentificationRequired T b
  muAut : S2219PaperOUnitsMu T b ≃* S2219PaperOUnitsMu T b
  unitLift : S2249LogKummerOnUnitsRequired T b
  attachment : S2222PaperOUnitsMuAttachment T b
  logKummer : S2245LogKummerRequired T b
```

Under `h : S2135PrimeAlignmentRequired T b` every component is constructed:

```lean
noncomputable def s2321OUnitsChainOfPrimeAlignment
    (h : S2135PrimeAlignmentRequired T b) : S2321OUnitsChain T b
```

and the remaining input is exactly S2135:

```lean
theorem s2321Chain_iff_primeAlignment :
  Nonempty (S2321OUnitsChain T b) ↔ S2135PrimeAlignmentRequired T b
def S2321RemainingRequired : Prop := S2135PrimeAlignmentRequired T b
```

S2232 records that the arbitrary source clauses do not imply
`qVFamTensorP T b ∈ primeStrip 2 7`; this is the single exact remaining input.
It is available for the concrete S1730 bad set but not for arbitrary T.

```
file:   tmp/sheaf/xif/paper/S2321OUnitsChainFinalActual.lean
EXIT=0; SHA256=A84C143DFE400316EFC9E2499E5A060952FFD8D9E8B9DD69E25AF9F26603548C
olean: yes
```

## S2324: S2135 decision status

`tmp/sheaf/xif/paper/S2324S2135DecideActual.lean` reduces S2135 to the numeric
condition and records the exact universal/counterexample alternatives.

```lean
theorem s2324_not_strip_iff_gt_seven :
  ¬ S2135PrimeAlignmentRequired T b ↔ 7 < qVFamTensorP T b
```

```lean
def S2324Universal : Prop :=
  ∀ T b, qVFamTensorP T b ≤ 7

structure S2324CounterexampleRequired where
  T : SourceNativeInitialThetaData l
  b : Bad (nativePlaceSelection T)
  gt_seven : 7 < qVFamTensorP T b
```

Actual dichotomy:

```lean
theorem s2324_dichotomy :
  S2324Universal ∨ Nonempty S2324CounterexampleRequired
```

A counterexample refutes S2135 (`s2324_counterexample_not_strip`), while a
universal bound makes the whole S2321 chain unconditional
(`s2324_chain_universal_of_universal`).

Source obstruction: `s2324_prime_above_seven` proves primes above 7 exist;
S2232 proves the source clauses (oddness/coprimality) do not bound the rational
prime, so the universal statement is not derivable from the current source
audit.  Constructing a full concrete `SourceNativeInitialThetaData` with a bad
place of residue characteristic > 7 is not available in the tree; no such T is
fabricated.

Exact missing decision datum:

```lean
def S2324DecisionRequired : Prop :=
  Nonempty (S2324CounterexampleRequired l) ∨
    ∀ T b, Nonempty (S2321OUnitsChain T b)
```

```
file:   tmp/sheaf/xif/paper/S2324S2135DecideActual.lean
EXIT=0; SHA256=CD46005EA1BAE1EA2A074074B887784D84101260231068E3912D3FC67022BBB5
olean: yes
```

## S2331: concrete S1730/S1667 model audit

`tmp/sheaf/xif/paper/S2331S2135ModelsActual.lean` audits the concrete models.

- The concrete S1730 bad set consists of rational places with residue
  characteristics 3, 5, 7, all inside `primeStrip 2 7`
  (`s2331_concrete_bad_residue_mem_primeStrip`).
- Any model whose bad F-place has one of those residue characteristics satisfies
  S2135 (`s2331_S2135_of_S1730Model`), hence the concrete S1730 places cannot
  refute S2135.
- The source constraints themselves still allow odd primes outside the strip:
  `s2331_source_allows_outside_strip`.

Exact missing counterexample object:

```lean
structure S2331CounterexampleTRequired (l) where
  T : SourceNativeInitialThetaData l
  b : Bad (nativePlaceSelection T)
  gt_seven : 7 < qVFamTensorP T b
```

No inhabitant.  `s2331_counterexample_refutes` shows such an object would refute
S2135; no such full concrete T is available in the tree.  This confirms S2135 is
not decided by the existing concrete models.

```
file:   tmp/sheaf/xif/paper/S2331S2135ModelsActual.lean
EXIT=0; SHA256=EE808F2F4646A510A98CC2DA4CC933546487E1C743683B98ED2A995822C4736D
olean: yes
```

## S2362: fixed-C mainline readout and exact C1 gap

`tmp/sheaf/xif/paper/S2362MainlineReadoutActual.lean` interfaces the fixed-C
3.12 readout:

```lean
structure S2362FixedCData (P : PaperSignedHull X label) where
  qPilotLogVolume : Real
  qPilotLogVolume_eq_neg_abs : Prop
  xi_f_inequality : qPilotLogVolume ≤ P.signedHullLogVolume
```

An actual output readout is

```lean
structure S2362ActualOutputReadout (P) (F : S2362FixedCData P) where
  Output : Type u
  P_C : Set Output
  nu_C : Output → Real
  Q_C : Real
  Q_C_eq_qPilot : Q_C = F.qPilotLogVolume
  D : Output
  D_mem : D ∈ P_C
  readout_eq : nu_C D = Q_C
```

This gives the scalar step

```lean
s2362_qPilot_le_hull : R.Q_C ≤ P.signedHullLogVolume
s2362_hull_logVolume_lt_top : P.ambient.logVolume P.ambient.hull < ⊤
s2362_mainline_scalar : R.Q_C ≤ H_C ∧ H_C < ⊤
```

Exact missing C1/xi-f projection:

```lean
structure S2362C1OutputReadoutProjectionRequired (P) (F) where
  Output : Type u
  P_C : Set Output
  nu_C : Output → Real
  Q_C : Real
  Q_C_eq_qPilot : Q_C = F.qPilotLogVolume
  exists_output : ∃ D, D ∈ P_C ∧ nu_C D = Q_C
```

and the U2K2-to-P_C interface gap `S2362U2K2ToPCRequired` records the same
transport/membership/readout obligations as Props.  Given an exact projection,
`s2362ReadoutOfProjection` builds the actual readout and
`s2362_mainline_scalar_of_projection` yields `Q_C ≤ H_C` and finiteness.

No `D`, `nu_C(D)=Q_C`, or U2K2→P_C map is fabricated.  The C9 notes identify
this as `XiEToXiFOutputReadoutProjection`/C1 open.

```
file:   tmp/sheaf/xif/paper/S2362MainlineReadoutActual.lean
EXIT=0; SHA256=4F9C81018B5F9C236ABA829D21D89FE777C7F728E2A6BFE5A8C96F9644A74742
olean: yes
```

## S2373: C1 readout from the actual C9 output profile

`tmp/sheaf/xif/paper/S2373C1ReadoutActual.lean` uses the actual C9 output
carrier and profile log-volume:

```lean
def s2373Nu (R) (O : ActualOutput R) : Real :=
  R.input.profile.logVolume O.source

theorem s2373_actual_readout (b : BridgeOutput) :
  ∃ D : ActualOutput R,
    D ∈ b.possibleOutputs ∧ s2373Nu R D = s2373Nu R b.out
```

The witness is the actual output `b.out`; its membership is
`out_mem_possibleOutputs b`.  Thus the actual output carrier and readout exist.
The remaining C1/xi-f datum is exactly the equality of this actual readout with
the q-pilot scalar:

```lean
structure S2373QMarkReadoutEqRequired (b : BridgeOutput) where
  qPilotLogVolume : Real
  readout_eq : s2373Nu R b.out = qPilotLogVolume
```

No inhabitant.  Given it, the S2362 projection is constructed:

```lean
s2373Projection (b) (E : S2373QMarkReadoutEqRequired b)
  (hQ : F.qPilotLogVolume = E.qPilotLogVolume) :
  S2362C1OutputReadoutProjectionRequired p F
```

This uses `Output = ActualOutput R`, `P_C = b.possibleOutputs`,
`nu_C = s2373Nu R`, and `D = b.out`; no output or readout equality is fabricated.

```
file:   tmp/sheaf/xif/paper/S2373C1ReadoutActual.lean
EXIT=0; SHA256=F4E0A9E0947CD2F6EE6BAB23C0B24A38B0FA49A8706225E928300488B04C534F
olean: yes
S2362 revised SHA256: B35DDD45529DB1E386A866DCEE05963A23261A0C277EE447034EE7D767A74A46
```

## S2391: q-mark readout equality is not definitional

`tmp/sheaf/xif/paper/S2391QMarkReadoutActual.lean` unfolds the actual C9
readout and the source q-pilot scalar.

```lean
theorem s2391_readout_unfold :
  s2373Nu R b.out = R.input.profile.logVolume b.out.source := rfl

theorem s2391_out_source_eq_base :
  b.out.source = R.input.core.base := b.out.source_eq
```

The q-pilot scalar is `sourceQPilotSignedLog I.initial` (`- sum_b |log q_b|`,
from `PaperQPilotObject`), while the output readout is the independent
`profile.logVolume` at `b.out.source`.  No definitional identity identifies the
two; this is exactly the C9 source readout projection, not a `rfl` equality.

Exact missing data:

```lean
structure S2391SourceReadoutRequired (b : BridgeOutput) where
  qPilotLogVolume : Real
  qPilot_eq : qPilotLogVolume = sourceQPilotSignedLog I.initial
  readout_eq : R.input.profile.logVolume b.out.source = qPilotLogVolume
```

No inhabitant.  If the equality is supplied, the S2373 readout equality and
the S2362 projection follow:

```lean
s2391QMarkReadoutEqOfSourceEq
s2391ProjectionOfSourceEq
```

```
file:   tmp/sheaf/xif/paper/S2391QMarkReadoutActual.lean
EXIT=0; SHA256=C7B2CE22873401A9D24F086BCA2000AE5916B1739E518002E965AD3611C9DCF2
olean: yes
```

## S2396: source readout audit

`tmp/sheaf/xif/paper/S2396SourceReadoutAuditActual.lean` audits the actual
source structures.

- `SourceTheorem311Realization` has no q-pilot scalar field.  Its profile is the
  packet log-volume: `s2396_realization_profile_eq_packet :
  R.input.profile.logVolume c = R.packet.logVolume c`.
- `ActualOutput R = Theorem311Output R.input` (`s2396_actualOutput_eq_output`);
  its fields are the three theorem parts plus `source`, with no q-pilot scalar.
- `BridgeOutput` has only the layer/reference outputs, singleton possible-output
  set, and the explicit `C1SourceBridge` (`s2396_bridgeOutput_components`); no
  profile=q-pilot field.

The only source compatibility equation in the tree is the theta-packet one in
`sourceProcessionRecordIntendedCarrierCard: C_T.profile.logVolume C_T.core.base =
T.thetaPacket.logVolume`, not the q-pilot scalar.  The source text defines the
q-pilot object from the arithmetic divisor of the q_v and its log-volume
`-|log(q)|`; the multiradial comparison with the profile/hull log-volume is the
open C9 source statement.

Exact missing paper-level C9 input:

```lean
structure S2396ProfileQPilotBridgeRequired (b : BridgeOutput) where
  qPilotLogVolume : Real
  qPilot_eq : qPilotLogVolume = sourceQPilotSignedLog I.initial
  profile_readout_eq :
    R.input.profile.logVolume b.out.source = qPilotLogVolume
```

No inhabitant.  It yields the S2391 source readout datum via
`s2396SourceReadoutOfBridge`.

```
file:   tmp/sheaf/xif/paper/S2396SourceReadoutAuditActual.lean
EXIT=0; SHA256=1AC51CDAE73C3EC5D7126FE06EE85F47D39F652ACAC2A8ECFD8B3FABFCA04291
olean: yes
```

## S2401: C1SourceBridge/qPilotAsOutput audit

`tmp/sheaf/xif/paper/S2401C1BridgeAuditActual.lean` proves that the C1 bridge
forks the q-pilot output to the bridge output:

```lean
theorem s2401_qPilotOutput_eq_out :
  b.qPilotAsOutput.qPilotOutput = b.out
```

because `possibleOutputs = {b.out}`.  Consequently

```lean
theorem s2401_qPilotOutput_profile_eq :
  R.input.profile.logVolume b.qPilotAsOutput.qPilotOutput.source =
    R.input.profile.logVolume b.out.source
```

So the C1 membership gives no new readout value: it is the same profile
log-volume as `b.out`.  The source scalar is the independent

```lean
theorem s2401_sourceQPilot_def :
  sourceQPilotSignedLog I.initial = -sourceBadQAbsLog I.initial
```

(a sum of `|log q_b|`).  No existing field or theorem identifies it with the
profile value.

Exact paper-level interface on the q-pilot output:

```lean
structure S2401QPilotOutputReadoutRequired (b : BridgeOutput) where
  qPilotLogVolume : Real
  qPilot_eq : qPilotLogVolume = sourceQPilotSignedLog I.initial
  readout_eq :
    R.input.profile.logVolume b.qPilotAsOutput.qPilotOutput.source =
      qPilotLogVolume
```

No inhabitant; it yields the S2396 bridge via `s2401BridgeOfQPilotOutput`.

```
file:   tmp/sheaf/xif/paper/S2401C1BridgeAuditActual.lean
EXIT=0; SHA256=F052BC162E5E87C705AD92B87BF040E0997F4F45AF0572A98FF9A8EDB79AEBFA
olean: yes
```

## S2404: arithmetic form of the q-pilot gap

`tmp/sheaf/xif/paper/S2404QPilotArithmeticActual.lean` defines the actual
candidate readout

```lean
def s2404CandidateQPilotLogVolume (b) : Real :=
  R.input.profile.logVolume b.qPilotAsOutput.qPilotOutput.source
```

and proves

```lean
s2404_candidate_eq_out :
  candidate = R.input.profile.logVolume b.out.source
s2404_candidate_eq_packet :
  candidate = R.packet.logVolume b.out.source
s2404_sourceQPilot_eq_neg_sum :
  sourceQPilotSignedLog I.initial = -sourceBadQAbsLog I.initial
```

The C1 readout structure is exactly the single arithmetic identity

```lean
def S2404QPilotProfileIdentity (b) : Prop :=
  sourceQPilotSignedLog I.initial = s2404CandidateQPilotLogVolume b

theorem s2404_readoutRequired_iff_identity :
  Nonempty (S2401QPilotOutputReadoutRequired b) ↔
    S2404QPilotProfileIdentity b

theorem s2404_identity_iff_packet :
  S2404QPilotProfileIdentity b ↔
    sourceQPilotSignedLog I.initial = R.packet.logVolume b.out.source
```

The source side is `-sum_b |log q_b|`; the output side is the packet/profile
log-volume at `b.out.source`.  Theta-packet comparison is not a q-pilot
comparison.  The identity is therefore the exact paper-level arithmetic input:

```lean
structure S2404QPilotArithmeticRequired (b) where
  arithmetic_identity : S2404QPilotProfileIdentity b
```

No inhabitant.  It yields the S2401 readout datum via
`s2404ReadoutOfIdentity`.

```
file:   tmp/sheaf/xif/paper/S2404QPilotArithmeticActual.lean
EXIT=0; SHA256=130D74F4B276B14CA9DF487D04E7432991C18505865340FF81B4261FF1ECBDB5
olean: yes
```

## S2417: actual-prime O^× interface at qVFamTensorP

`tmp/sheaf/xif/paper/S2417ActualPrimeInterface.lean` packages the S2268/S2280
actual-prime units interface.  The prime is `s2268p = qVFamTensorP` with the
unconditional equality `s2280_sectionKPlace_prime_eq_qVFamTensorP`.

```lean
noncomputable def s2417OUnitsAtSectionKPlace :
  S2219PaperOUnits T b ≃* LocalOFieldUnits (s2268p T b)

noncomputable def s2417OUnitsMuAtSectionKPlace :
  S2219PaperOUnitsMu T b ≃*
    TimesMuQuotient (LocalOFieldUnits (s2268p T b))

structure S2417ActualPrimeOUnits (T b) where
  prime : Nat
  prime_eq : prime = qVFamTensorP T b
  [primeFact : Fact (Nat.Prime prime)]
  OUnitsEquiv : S2219PaperOUnits T b ≃* LocalOFieldUnits prime
  OUnitsMuEquiv : S2219PaperOUnitsMu T b ≃*
    TimesMuQuotient (LocalOFieldUnits prime)

noncomputable def s2417ActualPrimeOUnits : S2417ActualPrimeOUnits T b
```

Thus the unit/O^×μ interface is unconditional and does not need
`qVFamTensorP ≤ 7`.

The 3.12 Kummer arrow is indexed by `LocV = FinitePrimePlace 2 7`, so a Kummer
index at `qVFamTensorP` is a paper place `v` with `v.1 = qVFamTensorP`:

```lean
def S2417KummerPrimeIndexRequired : Prop :=
  ∃ v : LocV, v.1 = qVFamTensorP T b

theorem s2417KummerPrimeIndex_iff_S2135 :
  S2417KummerPrimeIndexRequired T b ↔ S2135PrimeAlignmentRequired T b
```

Given such an index, the S2268 local bridge transports `actualOUnitsMu v` to the
sectionKPlace prime quotient:

```lean
s2417KummerBridgeOfIndex (v) (hv) :
  actualOUnitsMu v ≃*
    TimesMuQuotient (LocalOFieldUnits (s2268p T b))
```

Consumer audit:

```lean
theorem s2417KummerConsumerAudit :
  Nonempty (S2417ActualPrimeOUnits T b) ∧
    (S2417KummerPrimeIndexRequired T b ↔ S2135) ∧
    (∀ v hv, Nonempty (actualOUnitsMu v ≃* ...))
```

So the p≤7 model obligation is bypassed for the actual unit interface; the
Kummer-arrow consumer still forces the S2135 index condition.

```
file:   tmp/sheaf/xif/paper/S2417ActualPrimeInterface.lean
EXIT=0; SHA256=8D119729A29E92F5B2C0AA0806F25B0FB42A92EE1745AA0ADB1720FA25265489
olean: yes
```

## S2422: 3.12 mainline integration (actual-prime + C1/hull)

`tmp/sheaf/xif/paper/S2422MainlineC9Actual.lean` integrates the actual-prime
interface, the Kummer-index gap, the qPilot arithmetic identity, and the C1
readout-to-hull chain.

(A) Actual-prime unit interface is unconditional:

```lean
structure S2422UnitInterface (T b) where
  actualPrime : Nat
  prime_eq : actualPrime = qVFamTensorP T b
  [primeFact : Fact (Nat.Prime actualPrime)]
  unitQuotient : S2219PaperOUnitsMu T b ≃*
    TimesMuQuotient (LocalOFieldUnits actualPrime)

noncomputable def s2422UnitInterface : S2422UnitInterface T b
```

with `actualPrime = s2268p`, `prime_eq = s2280_sectionKPlace_prime_eq_qVFamTensorP`.
No `p ≤ 7`.

The actual Kummer arrow is indexed by `LocV = FinitePrimePlace 2 7`;
`S2422KummerConsumptionAtPrime` adds the index `v` with
`v.1 = unitInterface.actualPrime`.  The index exists exactly under S2135:

```lean
theorem s2422KummerIndex_iff_S2135 :
  (∃ v : LocV, v.1 = qVFamTensorP T b) ↔ S2135PrimeAlignmentRequired T b
```

(C) The S2404 arithmetic identity gives the profile readout, hence the C1
projection and the signed-hull inequality:

```lean
theorem s2422_profile_eq_source (E : S2404QPilotArithmeticRequired b) :
  R.input.profile.logVolume b.out.source = sourceQPilotSignedLog I.initial

noncomputable def s2422C1ProjectionOfArithmetic
  (E : S2404QPilotArithmeticRequired b)
  (hQ : F.qPilotLogVolume = sourceQPilotSignedLog I.initial) :
  S2362C1OutputReadoutProjectionRequired p F

theorem s2422_qPilot_le_hull_of_arithmetic
  (E) (hQ) :
  (s2362ReadoutOfProjection (s2422C1ProjectionOfArithmetic b E hQ)).Q_C ≤
    p.signedHullLogVolume ∧
  p.ambient.logVolume p.ambient.hull < ⊤
```

Thus the paper-level 3.12 prerequisite chain is actual up to exactly:
- `S2404QPilotArithmeticRequired b` (C9 qPilot/profile arithmetic identity);
- `S2135PrimeAlignmentRequired T b` for the actual Kummer arrow index;
- the paper q-pilot object binding / xi-f output-readout projection.

Source audit (subagent, IUT-III.txt SHA256 822E03DA...): IUT III defines the
q-pilot object (Def 3.8) and its normalized log-volume, and proves the
hull/determinant/log-volume inequality `-|log Θ| >= -|log q|` (Cor 3.12).
It does not construct `profile.logVolume(output) = -Σ_b |log q_b|`; the closest
statements are the SHE condition (xi-e) and the xi-f assertion "perhaps only up
to approximation".  The exact paper-level missing inputs are:
1. q-pilot scalar normalization `-|log q|` = bad-place sum with local factors;
2. xi-f output-readout projection (or at least the input pilot-object log-volume
   equality);
3. q-pilot object binding to the reduced `sourceQPilotStrip` anchor.

```
file:   tmp/sheaf/xif/paper/S2422MainlineC9Actual.lean
EXIT=0; SHA256=766FAEBC6F058871047D3A4497AC73ED8043B256BF3CD5C2BBC5AC2D9B05CF20
olean: yes
```

## S2440: C9 source inputs and actual bad-q scalar object

`tmp/sheaf/xif/paper/S2440C9SourceInputsActual.lean` does two things.

(1) ACTUAL construction from the bad q family:

```lean
theorem s2440_sourceQPilot_eq_neg_bad_sum :
  sourceQPilotSignedLog I.initial =
    -(∑ b : I.initial.badPlaces,
      |Real.log (I.initial.reduction.qParameter b)|)

structure S2440ActualQPilotScalarObject where
  badQFamily : I.initial.badPlaces → Real
  badQFamily_eq : ∀ b, badQFamily b = I.initial.reduction.qParameter b
  qPilotLogVolume : Real
  qPilotLogVolume_eq_source :
    qPilotLogVolume = sourceQPilotSignedLog I.initial
  qPilotLogVolume_eq_bad_sum :
    qPilotLogVolume = -(∑ b, |Real.log (badQFamily b)|)

noncomputable def s2440ActualQPilotScalarObject :
  S2440ActualQPilotScalarObject
```

This is the actual q-pilot scalar object from the actual `q_v`/bad places; no
paper normalization or profile equality is assumed.

(2) Exact paper-level C9 inputs, no inhabitant:

```lean
structure S2440QPilotScalarNormalizationRequired (O) where
  paper_log_identification : O.paper_qPilot_log_identification
  paperNormalized : Real
  paperNormalized_eq_bad_sum :
    paperNormalized = -sourceBadQAbsLog I.initial
  candidate_eq_paper :
    sourceQPilotSignedLog I.initial = paperNormalized

structure S2440QPilotObjectBindingRequired (O) where
  strip_identification : O.paper_strip_identification
  lineBundle_identification : O.paper_lineBundle_identification
  logKummer_identification : O.paper_logKummer_identification
  qPilot_log_identification : O.paper_qPilot_log_identification

structure S2440XiFReadoutRequired (b) where
  exact_identity : S2440XiFExactIdentity b
```

Actual conditional links (not paper claims):

```lean
s2440_exact_iff_S2404 :
  S2440XiFExactIdentity b ↔ S2404QPilotProfileIdentity b
s2440_exact_implies_approx
s2440_qPilot_le_hull
```

Source audits (three read-only subagents, IUT-III SHA256 822E03DA...):
- q-pilot object is the Def 3.8(i) divisor object/prime-strip, not the reduced
  `sourceQPilotStrip`; T5 remains open.
- `-|log q|` is defined as a procession-normalized log-volume; the paper gives
  local formulas and defers the explicit bad-place computation to IUT-IV §1.
- Cor 3.12 gives only the inequality `-|log Θ| >= -|log q|`; xi-f's
  "approximation" is qualitative, and the pointwise profile equality is not in
  the source.  The exact missing leaf is the paper-family output readout
  projection/coverage, not a theorem of Theorem 3.11 data.

```
file:   tmp/sheaf/xif/paper/S2440C9SourceInputsActual.lean
EXIT=0; SHA256=AEE72553A2EFD3916AB5A7072F7D6EEA946A44071302D9F0FA58264769A6270B
olean: yes
```

## S2441: actual fixed-Type paper q-pilot carrier and piloted T5 binding

`tmp/sheaf/xif/paper/S2441C9PaperCarrierActual.lean` builds on S1979's actual
piloted strip and removes the vacuous Prop-valued self-equality slots.

```lean
structure S2441PaperQPilotCarrier (D : S1895PaperInput) where
  pilotedStrip :
    PilotedFTimesMuPrimeStrip PaperV (paperInput D).initial.badPlaces
  pilotedStrip_eq : pilotedStrip = paperQPilotPilotedStrip D
  pilotObject : IUTIVArithmeticDivisor (PaperFmod D)
  pilotObject_eq :
    pilotObject = associatedPilotObject D pilotedStrip
  pilotObject_eq_paper : pilotObject = paperQPilotDivisor D

noncomputable def s2441PaperQPilotCarrier (D) : S2441PaperQPilotCarrier D
```

Actual fields: q_v-compatible generators, Def 3.8(i) associated divisor, and the
paper divisor identification.  No Prop fields.

```lean
theorem s2441_generator_value_eq_log :
  pilotGeneratorRealifiedValue (paperQPilotPilotedStrip D) b =
    Real.log (paperQV D b)
theorem s2441_pilotObject_deg :
  deg (associatedPilotObject D (paperQPilotPilotedStrip D)) =
    sourceBadQAbsLog (paperInput D).initial
```

Fixed-Type piloted T5 binding:

```lean
structure S2441PilotedT5Binding (D) where
  carrier : S2441PaperQPilotCarrier D
  reducedStrip : SourceFTimesMuPrimeStrip PaperV
  reducedStrip_eq : reducedStrip = reducedQPilotTimesMu D
  sourceAnchor : FPrimeStrip PaperV
  sourceAnchor_eq :
    sourceAnchor = sourceQPilotStrip (S1895PaperO D).boundary
  projection_eq :
    carrier.pilotedStrip.toSourceFTimesMuPrimeStrip = reducedStrip
  pilotedIdentification :
    PilotedQPilotAnchorIdentification D carrier.pilotedStrip

noncomputable def s2441PilotedT5Binding (D) : S2441PilotedT5Binding D
```

The source anchor is definitionally `sourceQPilotStrip (S1895PaperO D).boundary`;
the piloted identification includes the generator compatibility, so the q_v
generators are not lost (contrast the unit-generator strip of S1979).

Exact remaining paper-level scalar normalization:

```lean
structure S2441QPilotPaperNormalizationRequired (D) where
  paperNormalized : Real
  rootFactor : Real
  rootFactor_eq : rootFactor = (2 * (D.l.value : Real))⁻¹
  weightedMagnitude : Real
  paperNormalized_eq : paperNormalized = -rootFactor * weightedMagnitude
  candidate_eq_paper :
    sourceQPilotSignedLog (paperInput D).initial = paperNormalized
```

No inhabitant.  Source audit (IUT-III SHA 822E03DA...; IUT-IV): the paper scalar
is `|log q| = (1/(2l)) * (1/[F:Q]) * Σ_v ord_v(q_v) * log(#k_v)` with
Rem 3.1.1(ii)/2.4.2(ii) weights and Prop 3.9(i) procession average.  The Lean
candidate `sourceQPilotSignedLog = -Σ_b |log q_b|` lacks the `1/(2l)` factor,
the normalized-degree/local weights, the procession average, and the
`qParameter ↔ q_v`, `badPlaces ↔ V_bad` bridges.

Literal `O^▷(A) ⊆ O^◃(A)` generator pro-object data remains missing; S1979's
piloted strip is the maximal actual carrier available.  No fake.

```
file:   tmp/sheaf/xif/paper/S2441C9PaperCarrierActual.lean
EXIT=0; SHA256=45B85F384AE5E5C5F89305D359A6D0D25403392CEE47A50C8168E7FC7F895C04
olean: yes
```

### S2441 concrete normalization theorem

The S1895 concrete model now has an actual normalization theorem, computed from
the actual q_v orders:

```lean
theorem s2441_concrete_normalization (D : S1895PaperInput) :
  sourceQPilotSignedLog (paperInput D).initial =
    -((S1487Cand.order : Real) * Real.log 5)

theorem s2441_concrete_divisor_deg (D : S1895PaperInput) :
  IUTIVArithmeticDivisor.deg (F := PaperFmod D)
    (paperQPilotDivisor D) =
      (S1487Cand.order : Real) * Real.log 5
```

So for the concrete S1895 model the q_v/order computation is actual.  The
general paper normalization (`1/(2l)`, `1/[F:Q]`, local residue weights,
procession average, qParameter↔q_v, badPlaces↔V_bad) remains the exact missing
`S2441QPilotPaperNormalizationRequired`; no general inhabitant is asserted.

S2441 final SHA256: 58B0AF92BFEF79F05D9FE1ED06EA909D33FACAB8E14B3248AC9475E33D45B919

## BUILD INCIDENT hold — C9 status freeze (2026-11-03)

All `lake env lean` / `lake build` commands stopped on build-coordinator notice:
Mathlib artifacts missing (`LibraryRewrite.olean`, `Bochner/Set.olean`,
`UniformField.olean`), likely concurrent build contention. No new compiles
launched. Current proof state only:

### Accepted before hold
- S2422MainlineC9Actual.lean: EXIT=0, olean yes,
  SHA256 766FAEBC6F058871047D3A4497AC73ED8043B256BF3CD5C2BBC5AC2D9B05CF20.
- S2440C9SourceInputsActual.lean: EXIT=0, olean yes,
  SHA256 AEE72553A2EFD3916AB5A7072F7D6EEA946A44071302D9F0FA58264769A6270B.
- S2441C9PaperCarrierActual.lean v2: EXIT=0, olean yes,
  SHA256 58B0AF92BFEF79F05D9FE1ED06EA909D33FACAB8E14B3248AC9475E33D45B919.
  Axioms probe for the new concrete normalization declarations was repeatedly
  blocked by transient Mathlib `.olean.private` read errors before the build
  hold; NOT yet trio-verified.  Earlier S2441 declarations were trio-verified.

### Actual, kernel-checked (S2441)
- `S2441PaperQPilotCarrier` fixed-Type carrier: piloted strip, actual q_v
  generators, Def 3.8(i) divisor, `paperQPilotDivisor` equality.
- `S2441PilotedT5Binding`: sourceQPilotStrip anchor (rfl), reduced strip,
  generator-compatible piloted identification.
- `s2441_concrete_normalization`:
  `sourceQPilotSignedLog (paperInput D).initial =
    -((S1487Cand.order : Real) * Real.log 5)`.
- `s2441_concrete_divisor_deg`:
  `deg (paperQPilotDivisor D) = order * log 5`.

### Pending exact missing (no inhabitant)
- `S2441QPilotPaperNormalizationRequired`: general paper normalization factors
  `1/(2l)`, `1/[F:Q]`, local residue weights, Prop 3.9(i) procession average,
  qParameter↔q_v, badPlaces↔V_bad, literal O^▷ pro-generators.
- `S2440QPilotObjectBindingRequired` / `S2440XiFReadoutRequired`.
- xi-f paper family `P_C, ν_C, Q_C=-|log q|`, exact or signed-ε coverage.

### Next actions after build coordinator clearance
1. Rerun `#print axioms` for all S2441 new declarations and report trio/dirty.
2. Construct/refute general normalization; use S1487 two-place scalar
   difference as evidence against single-completion surrogate; record exact
   missing or corrected formula.
3. Construct xi-f paper-family coverage or keep exact missing.

## S2448/S2450/S2451/S2452 — C9 general normalization + xi-f execution (post-lock)

### S2450 (actual normalization calculation)
- `S2450BadPlaceMap` inhabited: place=b.1.maximalIdeal, q_v=paperQV, order=paperQVOrder, residueWeight=log5.
- `gaussianField_finrank_two : Module.finrank Q GaussianField = 2`;
  `paperFmod_finrank_two : Module.finrank Q (PaperFmod D) = 2`.
- `paperNormalizedSignedLog D = -(order*log5)/(4*l)` and
  `sourceQPilotSignedLog_ne_paperNormalizedSignedLog` (raw source = -order*log5).
- `s2450GeneralNormalizationRequired_impossible :
  ¬ Nonempty (S2450GeneralNormalizationRequired D)`.
  KEY FINDING: the naive paperNormalized=source equality is FALSE on S1895;
  the corrected actual scalar is -C/(4l), C=order*log5.

### S2448 (actual bad-place/root-factor skeleton)
- `s2448BadPlaceMap`; `paperRootFactor=(2l)^-1`; `s2448_raw_ne_twoLCorrected`.
- exact missing `S2448GeneralNormalizationRequired` (no inhabitant).

### S2451 (Prop 3.9(i) average)
- Actual `paperProcessionQPilotLogVolume` over l* capsules / F_l^x labels,
  diagonal equality = paperQPilotLogVolume = sourceQPilotSignedLog.
- exact missing `S2451ProcessionAverageRequired` for the non-diagonal
  per-capsule q-pilot family/weighted average identification; no inhabitant.

### S2452 (xi-f interface)
- Exact/signed coverage consumers from S1447:
  `s2452_Q_C_le_of_upper_coverage`.
- `S2452PaperOutputFamily` exact paper-family interface (P_C, nu_C,
  Q_C=-|log q|, readout_eq, upper, coverage); no constructor/inhabitant.
- `S2452PaperOutputFamilyRequired` no inhabitant; consumer conditional only.
- Singleton bridge/value-layer qMark NOT used as paper P_C/Q_C.

All four files EXIT=0, olean yes, axioms trio [propext,Classical.choice,Quot.sound]:
- S2448 SHA A93A265BF0CE5C053BE658046C16DBB0ACAD523B163C4A2EBC591A61F2D56F43
- S2450 SHA 50A312A9088334BCB70E59FB4754E32E3F6C255399EF47D948A9E097FC742051
- S2451 SHA CE90A414F28A10C7EBDF4B5737B9491476AB22DB14EB81FCEB2EDC5BBC9576A8
- S2452 SHA 056BF18EC5E7B20C5F10E699404F21FC2ED9487DC129CFABC318F80CC04F1937

Conclusion: concrete paper normalization is actually computed (-C/(4l)) and
provably differs from raw sourceQPilotSignedLog; general equality is refuted on
the concrete model, not assumed.  Procession averaging is actual only in the
diagonal case; non-diagonal paper capsule family is exact missing.  xi-f paper
family/coverage remains exact missing; only the S1447 consumer is actual.

## S2455/S2456/S2457 — general normalization, paper family interface, coverage consumers

### S2455 GENERAL NORMALIZATION CANDIDATE (ACTUAL)
```lean
S2455GeneralPaperNormalized S := -(sourceBadQAbsLog S)/(4*l.value)
S2455GeneralPaperNormalized_eq_sum :
  = (-∑ b, |log qParameter b|)/(4*l.value)   -- actual q_v form
S2455GeneralPaperNormalized_paperInput (D) :
  S2455GeneralPaperNormalized (paperInput D).initial =
    S2450.paperNormalizedSignedLog D       -- concrete -C/(4l)
```
This is the actual general form from actual q_v data; it does NOT assert that
arbitrary S's paper normalization equals it.  Exact missing interface
`S2455GeneralNormalizationRequired` (place/weight/procession/paperNormalized
fields) has no inhabitant.

### S2456 PAPER FAMILY INTERFACE (EXACT MISSING)
`S2456ActualPaperFamilyRequired` records P_C/nu_C/Q_C=-|log q|/readout/upper/
coverage; no inhabitant.  `toS2452` and the equivalence
`Nonempty S2456 ↔ S2452PaperOutputFamilyRequired` prove the interface is exact.

### S2457 COVERAGE/READOUT CONSUMERS (ACTUAL CONDITIONAL)
- witness->coverage, exact/signed->coverage;
- `s2457_Q_C_le_of_upper_coverage`;
- paper-family consumers `s2457_paper_Q_C_le_signedHull`;
- `s2457FixedCDataOfPaperFamily` builds S2362FixedCData with xi_f_inequality
  PROVED from paper coverage; exact coverage yields S2362 C1 projection/readout;
- exact missing `S2457PaperCoverageRequired` = Nonempty S2452PaperOutputFamily,
  no inhabitant.

All files EXIT=0, olean yes, axioms trio [propext,Classical.choice,Quot.sound]:
S2455 SHA BDF88AE0AFEBA0F2A6BDFB4E54CE71002A3F4F0C3B68C2B386BA233D3A0DCEF3
S2456 SHA 55523885D0ECE4BE2D53E672219DC4E218C15BFE1BF1D1D990F1D255C71904EF
S2457 SHA 059F29794F6D022F2F2CA42F152782C39BD6FF9031E21CBD5F7E22AFF036D3D1

Remaining exact missing: arbitrary-S paper normalization identification
(S2455GeneralNormalizationRequired); non-diagonal procession average
(S2451ProcessionAverageRequired); actual paper family P_C/nu_C/coverage
(S2452/S2456/S2457Required); literal O^▷ pro-generators and T5 paper carrier.

### S2460 paper-family obstruction (ACTUAL)

`tmp/sheaf/xif/paper/S2460PaperFamilyObstructionActual.lean`:

```lean
theorem s2460_exact_coverage_obstruction
  (hread : ∀ D ∈ P_C, nu_C D = profile D)
  (hprof : ∀ D ∈ P_C, profile D = source)
  (hQ : Q_C = paper) (hne : source ≠ paper)
  (hcov : ∃ D ∈ P_C, nu_C D = Q_C) : False

theorem s2460_signed_coverage_obstruction
  (hread) (hprof) (hQ) (hlt : source < paper)
  (hcov : ∀ eps > 0, ∃ D ∈ P_C, Q_C - eps ≤ nu_C D) : False

theorem s2460_source_lt_paper (D) :
  sourceQPilotSignedLog (paperInput D).initial < paperNormalizedSignedLog D
```

Consequence: with the S2404/S2391 readout (profile = raw source scalar) and
the corrected paper scalar `-C/(4l)`, neither exact nor signed-epsilon coverage
can hold for the concrete S1895 model.  The old S2404-readout route is thus
obstructed; an actual paper family must construct a different P_C/nu_C, and
that construction remains missing.  No interface is asserted as actual.

S2460 EXIT=0, olean yes,
SHA 80A7CD6E7B442AB75C52386FBB74D748140ADE3D7BC09179723F4BAF4229D8D7,
axioms trio.

### S2465 paper-family forcing (ACTUAL)

`tmp/sheaf/xif/paper/S2465PaperFamilyForcingActual.lean`:

```lean
theorem s2465_family_exact_coverage_profile
  (F : S2452PaperOutputFamily P R)
  (h : S2452ExactCoverage F.P_C F.nu_C F.Q_C) :
  ∃ D ∈ F.P_C, R.input.profile.logVolume D.source = F.Q_C

theorem s2465_family_signed_coverage_profile
  (F) (h : S2452SignedCoverage F.P_C F.nu_C F.Q_C) :
  ∀ eps > 0, ∃ D ∈ F.P_C,
    F.Q_C - eps ≤ R.input.profile.logVolume D.source

theorem s2465_no_exact_family_of_source_readout
  (F) (hsource : ∀ D ∈ F.P_C, profile D = source)
  (hQ : F.Q_C = paper) (hne : source ≠ paper) :
  ¬ S2452ExactCoverage F.P_C F.nu_C F.Q_C
```

Consequence: a paper family with the S2404/S2391 source readout and the
corrected scalar -C/(4l) is impossible (exact and, when source<paper, signed).
Any actual paper P_C/nu_C must therefore use a genuinely different readout;
the tree contains no such construction.  S2465 EXIT=0, olean yes,
SHA DF7B1734D26DAC82281825AFF0931BB4DC21A977BBB29F63EC16369E9FF3FE59,
axioms trio.

### S2470 non-singleton capsule-family obstruction (ACTUAL)

`tmp/sheaf/xif/paper/S2470CapsuleFamilyObstructionActual.lean`:

```lean
theorem s2470_capsule_card_ge_two (D) :
  2 ≤ Fintype.card (S2451PaperCapsuleLabel D)

theorem s2470_capsule_exact_coverage_impossible (D) :
  ¬ S2452ExactCoverage
      (Set.univ : Set (S2451PaperCapsuleLabel D))
      (fun _ => paperQPilotLogVolume D)
      (paperNormalizedSignedLog D)

theorem s2470_capsule_signed_coverage_impossible (D) :
  ¬ S2452SignedCoverage
      (Set.univ : Set (S2451PaperCapsuleLabel D))
      (fun _ => paperQPilotLogVolume D)
      (paperNormalizedSignedLog D)
```

This is a concrete non-singleton family (actual capsule index, actual diagonal
q-pilot readout), not an interface.  It shows the natural capsule family cannot
cover the corrected paper scalar `-C/(4l)`, either exactly or by signed epsilon.
S2470 EXIT=0, olean yes,
SHA 1924560BC585C9CAC8808893329B727001C2B7275D82C5618EB97D9B388802BE,
axioms trio.

### S2475 S1473 actual value-layer inhabitant

S1473's `Carrier` universe was generalized (`Type uC`), removing the previous
Type-0 block.  `S2475S1473ValueLayerActual.lean` constructs an ACTUAL inhabitant
of `S1473PaperMarkedMap`:

```lean
noncomputable def s2475ValueLayerMarkedMap
  (hBdd : BddAbove (I.sourceThetaHullLogValueSet v R n)) :
  S1473PaperMarkedMap I v R n
```

with `Carrier := I.ThetaPilotPoint v`, `u_qv := id`, `g_q := readout I v`,
`finalEvaluationFamily := allowedOutputSource I v R n`; all fields are actual
S1447 theorems (`qMark_mem_allowedOutputSource`, `readout_qMark`,
`allowedOutputSource_subset_hull`/`le_csSup`).

This is a genuine inhabitant of S1473 but its Carrier is the value layer, not
`ActualOutput R`.  It does not construct the paper `P_C/nu_C`.  The exact
missing object is a map/identification from the value-layer theta-pilot carrier
to an `ActualOutput R` paper family with paper readout; no such data exist in
the tree.  S2475 EXIT=0, olean yes,
SHA 5104E0788F525DE1CFB3F9ABEC98522F3F275FA92B6F5722FEC3E477FA2189CA,
axioms trio.  S1473 revised SHA
1E157C76948BF6456F081073151D65044B965132FC1A757C030E377A0BAE7840.

### S2480 value-layer→ActualOutput map: exact missing

`tmp/sheaf/xif/paper/S2480ValueLayerToActualOutputRequired.lean` records the
exact missing map

```lean
structure S2480ValueLayerToActualOutputRequired (I v R3) where
  toOutput : I.ThetaPilotPoint v → ActualOutput R3
  profile_readout_compat : ∀ x,
    R3.input.profile.logVolume (toOutput x).source = readout I v x
```

No inhabitant.  The only actual map available is the constant map to a C9
output; its compatibility is proved to force the missing S2404 identity:

```lean
theorem s2480_constant_map_compat_forces_S2404
  (O : ActualOutput R3)
  (h : ∀ x, profile.logVolume O.source = readout I v x) :
  profile.logVolume O.source = I.sourceQPilotLogVolume v R n
```

Hence the constant-map route requires S2404, which S2460/S2465 show is
incompatible with the corrected paper scalar -C/(4l) for exact/signed coverage.
No nonconstant value-layer→ActualOutput map exists in the tree.

S2480 EXIT=0, olean yes,
SHA B86EEDFF17460B828D5EBC6063F0B7E314FB2DC8C41416AFF0909D815BCCFB22,
axioms trio.  S2475 actual value-layer S1473 inhabitant SHA
5104E0788F525DE1CFB3F9ABEC98522F3F275FA92B6F5722FEC3E477FA2189CA;
S1473 revised SHA 1E157C76948BF6456F081073151D65044B965132FC1A757C030E377A0BAE7840.

### S2490 literal O^▷ pro-generators obstruction (ACTUAL)

`tmp/sheaf/xif/paper/S2490LiteralOProObstructionActual.lean`:

```lean
theorem s2490_same_bare_strip (D) :
  (paperQPilotPilotedStrip D).toSourceFTimesMuPrimeStrip =
    (paperQPilotUnitGeneratorStrip D).toSourceFTimesMuPrimeStrip
theorem s2490_no_carrier_only_pilot_object (D) :
  ¬ ∃ F : SourceFTimesMuPrimeStrip PaperV → IUTIVArithmeticDivisor (PaperFmod D),
      F (paperQPilotPilotedStrip D).toSourceFTimesMuPrimeStrip = paperQPilotDivisor D ∧
      F (paperQPilotUnitGeneratorStrip D).toSourceFTimesMuPrimeStrip = 0
theorem s2490_piloted_binding_actual (D) :
  Nonempty (S2441PilotedT5Binding D)
```

The bare SourceFTimesMuPrimeStrip cannot determine the O^▷ pilot object: the
same carrier has q-pilot divisor and zero pilot object depending on the
generator layer.  Thus the missing datum is the literal O^▷(A) submonoid /
pro-generator data with rho_v, not a carrier-only construction.  The actual
piloted T5 binding of S2441 remains maximal.  S2490 EXIT=0, olean yes,
SHA 30F6636F25B89F33305DA608BD853944ED2EB4EB2EB3638EFC03074AE2F1C8C6,
axioms trio.

### S2500 categorical O^◃/O^▷ minimal data

`tmp/sheaf/xif/paper/S2500CategoricalOtriangleActual.lean`:

```lean
abbrev S2500ODiamond p := LocalIntegralMonoid p
abbrev S2500OTriangle p := (LocalIntegralMonoid p)ˣ
abbrev S2500EvaluatedUnits p := evaluatedUnitSubgroup p
noncomputable def S2500UnitEvaluation p :
  S2500OTriangle p →* S2500EvaluatedUnits p
-- injective and surjective actual
```

Actual local carriers: O^◃ is the nonzero integral-closure monoid;
O^▷ candidate is its unit group, with the actual evaluated-unit equivalence.

Minimal pro-system definition (no categorical pro-object API in Mathlib):

```lean
structure S2500ProSystem where
  Index : Type
  le : Index → Index → Prop
  le_refl / le_trans
  obj : Index → Type
  transition : ∀ {i j}, le i j → obj j → obj i
  transition_refl
```

Exact missing data, no inhabitant:

```lean
structure S2500UniversalCoverRequired where
  proSystem : S2500ProSystem
  toODiamond : ∀ i, proSystem.obj i → S2500ODiamond p
  oTriangleSubmonoid : ∀ i, Set (proSystem.obj i)
  oTriangleGenerator : ∀ i, proSystem.obj i
  oTriangleGenerator_mem
  generator_compat

structure S2500RhoVRequired where
  rho : S2500OTriangle p → Real
  rho_one / rho_mul
```

S2490's actual obstruction shows no carrier-only function can recover the
O^▷ pilot object; the literal universal-cover pro-object, O^▷ submonoid,
pro-generators and rho_v maps remain exact missing.

S2500 EXIT=0, olean yes,
SHA 318D0310D8A37BB7959446C83EB5F614AFB0D1A0AAC4B159EDB4337724296ED0,
axioms trio.

### S2501 actual finite-Galois inverse system

`tmp/sheaf/xif/paper/S2501UniversalCoverSystemActual.lean`:

```lean
abbrev S2501Index p : Type :=
  { L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]) //
    FiniteDimensional ℚ_[p] L ∧ IsGalois ℚ_[p] L }

def S2501Le (L M) : Prop := M.1 ≤ L.1   -- reverse inclusion
noncomputable def S2501ProSystem p : S2500ProSystem
```

Actual fields: index = finite-dimensional Galois intermediate fields; transition
= actual field inclusion M → L for M ≤ L; transition_refl proved.  This is the
concrete inverse-system side of the universal cover.

Still exact missing: finite-level O^◃ ring/monoid on each L, O^▷ submonoid and
pro-generators, generator_compat, rho_v maps.  S2500UniversalCoverRequired /
S2500RhoVRequired have no inhabitant.  S2490 obstruction excludes carrier-only
construction.

S2501 EXIT=0, olean yes,
SHA 472FD992A8C791BCA4F9ABDD2C5F1CF3F0725D82E9715EF201E7741DC771C9F1,
axioms trio.

### S2502 finite-level O^◃ carrier (ACTUAL)

`tmp/sheaf/xif/paper/S2502FiniteLevelODiamondActual.lean`:

```lean
noncomputable def S2502ValuationSubring (L) : Subring L.1 :=
  (integralClosure (Valuation.integer (ValuativeRel.valuation Q_p)) L.1).toSubring
noncomputable def S2502IntegralClosure (L) : Subring L.1
noncomputable abbrev S2502ODiamond (L) : Type := (S2502IntegralClosure p L)⁰
```

For every finite Galois intermediate field L, this is the actual nonzero
integral-closure monoid over the Q_p valuation subring.  S2502 EXIT=0, olean
yes, SHA C783FBE1F8A7283B07B6C6B9E00D179AC5474E7AC812652583490070C704EF44,
axioms trio.  toODiamond, O^▷ generators/compat and rho_v are being constructed
in S2503/S2504/S2505; exact missing remains if not derived.

### S2506 actual additive rho_v on O^◃

`tmp/sheaf/xif/paper/S2506RhoVActual.lean`:

```lean
noncomputable def S2506Rho (x : S2500ODiamond p) : Real :=
  Real.log ‖(x.1.1 : AlgebraicClosure Q_p)‖
theorem S2506Rho_one : S2506Rho p 1 = 0
theorem S2506Rho_mul :
  S2506Rho p (x * y) = S2506Rho p x + S2506Rho p y
```

This is an actual realified additive map on the O^◃ carrier.  Its restriction to
the missing O^▷ generator layer remains exact missing.  S2506 EXIT=0, olean yes,
SHA 8CCBB73952E5FBCABCEEF541291408EF392A00825BD94F7181D2B560C5D1C6CE,
axioms trio.

### C9 branch closure status

Actual: finite-Galois inverse system (S2501), finite-level O^◃ carriers (S2502),
additive rho on O^◃ (S2506), local O^◃/O^▷ candidates and evaluated-unit
equivalence (S2500), piloted T5 carrier binding (S2441).

Exact missing (no inhabitants): O^◃→LocalIntegralMonoid toODiamond on each
finite level; O^▷ submonoid/pro-generators/generator_compat;
S2500UniversalCoverRequired / S2500RhoVRequired; genuine paper P_C/nu_C on
ActualOutput and xi-f coverage.

Actual obstructions: S2490 (carrier-only O^▷ cannot recover the pilot object);
S2460/S2465 (S2404 source readout + corrected paper scalar cannot cover);
S2470 (non-singleton actual capsule family cannot exact/signed cover).

Thus the C9 branch cannot be closed from the current tree; the remaining data
are genuine paper-level/pro-object objects, not formal gaps of the existing
statements.

### S2504/S2505 actual O^▷ structures and rho inhabitant

S2504 `tmp/sheaf/xif/paper/S2504OTriangleGeneratorsActual.lean` (EXIT=0, olean
yes, SHA DF3F11A3F2B072BF3B211B39239E0782C6B5AFC1E6E77D718840657F0939AB5E):

```lean
S2504GeneratedSubmonoid p L g := Submonoid.powers g
structure S2504OTriangleLevelData p L where
  generator : S2502ODiamond p L
  generator_not_unit / powers_injective / submonoid_ne_top
S2504LevelSubmonoid_powLogEquiv :
  Multiplicative ℕ ≃* S2504LevelSubmonoid p D
structure S2504LevelTransition p h : Type
structure S2504ProGeneratorData p : Type
S2504ProGeneratorData_proSystem : S2500ProSystem
```

Actual O^▷ submonoid/powers structure and transition compatibility.  No level
generator is constructed (uniformizer/valuation API missing).

S2505 `tmp/sheaf/xif/paper/S2505RhoVActual.lean` (EXIT=0, olean yes, SHA
FB39790828DEE557D2A0FDAE37CC48A2F8B070A4E0F7ADF7B73324D3476CCECE):

```lean
S2505Rho x := Real.log ‖toAlgebraicClosureUnits x‖
S2505Rho_one / S2505Rho_mul / S2505Rho_nonpos
S2505RhoOnUnits_eq_zero
S2505RhoVUnitRestriction : S2500RhoVRequired p   -- ACTUAL inhabitant
```

`S2500RhoVRequired` now has an actual inhabitant: the unit restriction of rho
is zero.  This is the unit-level half, not the nontrivial pro-generator rho.
`S2500UniversalCoverRequired` remains uninhabited.

S2504 axioms for `S2504ProGeneratorData_map_submonoid` and
`S2504LevelSubmonoid_powLogEquiv`; S2505 axioms for `S2505Rho`,
`S2505Rho_mul`, `S2505RhoVUnitRestriction`: all trio only.

### S2503/S2508 actual universal cover completion

S2503 `tmp/sheaf/xif/paper/S2503FiniteLevelToODiamondActual.lean` (EXIT=0, olean
yes, SHA BD641470027EE8D964D40D36210D695803A6FE4AE75DDC6983106F64DF4004DE): actual monoid maps
toODiamond : S2502ODiamond p L →* S2500ODiamond p, finite-level transition
system `S2503FiniteProSystem : S2500ProSystem`, and compatibility with the
global map.

S2508 `tmp/sheaf/xif/paper/S2508UniversalCoverActual.lean` (EXIT=0, olean yes,
SHA 729260B13E40F0377E124A995576EE67A1D8A6679C0D50404CA4AF16A150DFA0):

```lean
S2508P (L) : S2502ODiamond p L.1   -- base p, actual nonzero integral element
S2508UniversalCover : S2500UniversalCoverRequired p
```

with proSystem = S2503FiniteProSystem, toODiamond = S2503ODiamondMap,
oTriangleSubmonoid = powers of p, oTriangleGenerator = p at every level,
generator_compat proved.  This is an actual inhabitant of
S2500UniversalCoverRequired, using the base uniformizer p as pro-generator
(not a trivial/fake generator).

S2505 `S2505RhoVUnitRestriction : S2500RhoVRequired p` is the actual unit-level
rho restriction; the generator values are `S2505GeneratorRho` applied to
S2508UniversalCover.

### S2509 actual generator rho on S2508 cover

`tmp/sheaf/xif/paper/S2509C9GeneratorActual.lean` (EXIT=0, olean yes,
SHA BBC518B7593BFFAEAF91161617AFA65A45D75E69C7F131F603F5887539D2953A):

```lean
noncomputable def S2509Cover : S2500UniversalCoverRequired p :=
  S2508UniversalCover p
noncomputable def S2509GeneratorRho
    (L : (S2509Cover p).proSystem.Index) : Real :=
  S2505GeneratorRho p (S2509Cover p) L
```

Actual pro-generator (base p) with actual realified generator values at every
finite level.  S2503/S2508/S2509 axioms trio only.

### S2510 actual conditional paper family from all outputs

`tmp/sheaf/xif/paper/S2510PaperFamilyCandidateActual.lean` (EXIT=0, olean yes,
SHA B422E78D2C350C5E35033A3C3CDC4C2341CF78FE5EF281C3B7D8C0BFF38C8D52):

```lean
theorem S2510_profile_const (D : ActualOutput R) :
  profile.logVolume D.source = profile.logVolume core.base

noncomputable def S2510PaperFamilyCandidate
  (hs : profile.logVolume core.base < 0)
  (hbound : profile.logVolume core.base ≤ P.signedHullLogVolume) :
  S2456ActualPaperFamilyRequired P R
```

Fields: P_C = Set.univ (all actual outputs), nu_C = profile readout,
Q_C = profile(base), q = exp(-profile(base)), exact coverage by
theorem311Output.  This is a genuine hard fill of the family structure from
the actual outputs; the two inequalities are the remaining paper-side inputs.
No fake q/P beyond the fixed actual profile.

### S2511/S2512: paper family iff the hull inequality

S2511 `tmp/sheaf/xif/paper/S2511PaperFamilyObstruction.lean` (EXIT=0, olean
yes, SHA F36618EDCAAFB84E7CD370110385C9180578FA8A776A9A968A4D5C0362EBD470):

```lean
theorem S2511_no_family_of_hull_lt
  (h : P.signedHullLogVolume < profile.logVolume core.base) :
  ¬ Nonempty (S2456ActualPaperFamilyRequired P R)
```

S2512 `tmp/sheaf/xif/paper/S2512PaperFamilySignedActual.lean` (EXIT=0, olean
yes, SHA 9A55F0B88E21DF3DD21CCA9E0734DCB1E78334EF332B5D37E1FD83F455C17245):

```lean
noncomputable def S2512PaperFamilySigned
  (hbound : profile.logVolume core.base ≤ P.signedHullLogVolume) :
  S2456ActualPaperFamilyRequired P R
```

Fields: P_C = Set.univ, nu_C = actual profile, exact coverage if the profile
value is negative, signed coverage otherwise; q = exp(-s) or 2.  Thus the paper
family exists exactly when the single actual inequality
`profile.logVolume(core.base) ≤ P.signedHullLogVolume` holds; S2511 proves the
reverse direction (failure of the inequality precludes any family).  The
remaining source input is exactly this hull inequality, not an interface.

### S2513 exact paper-family characterization

`tmp/sheaf/xif/paper/S2513PaperFamilyCharacterization.lean` (EXIT=0, olean yes,
SHA 80862ADA3BC2FADE18207A05B1599772DFEC3DDCEFE0A65E890326ECAAC4F420):

```lean
theorem S2513_family_iff_hull :
  Nonempty (S2456ActualPaperFamilyRequired P R) ↔
    profile.logVolume core.base ≤ P.signedHullLogVolume
```

This is the exact characterization: S2512 gives the family under the
inequality, S2511 proves failure precludes any family.  The remaining source
input is exactly the single hull inequality; no interface remains.

### Final paper-family source reduction

S2513 proves exactly:

```lean
Nonempty (S2456ActualPaperFamilyRequired P R) ↔
  profile.logVolume core.base ≤ P.signedHullLogVolume
```

The remaining source facts are:

1. `S2396ProfileQPilotBridgeRequired`: profile(core.base) = qPilot source scalar
   (S2396 records profile=packet actual, but profile=qPilot is not derived).
2. `PaperSourceBadQBound`: `P.procession.average ≤ sourceBadQAbsLog I.initial`
   (S624 records it as a Prop, no inhabitant), equivalently
   `sourceQPilotSignedLog ≤ P.signedHullLogVolume`.

Combining these two would prove the hull inequality and hence, by S2512, the
unconditional paper family.  Neither is available in the tree; no fake proof is
written.  The Q_C=-|log q| paper source-q identification remains S2440/S2455.

### D6 S2092 status

Actual files:

- S2091 scheme cancellation, EXIT=0/olean yes,
  SHA 21E06ED92492D99698840D142822620A20EC7CE1246AEB99F68E940B1C12DB58.
- S2089 reduction of stack cancellation to presentation+property,
  EXIT=0/olean yes,
  SHA C5E04AB9E409DF3B413B9BE7AFAB0AC875F2BB48B19232738DB8538C810E11DB.
- S2090 postcomposition-cancellation obstruction statement,
  EXIT=0/olean yes,
  SHA EE941E1A65CF4E954CB067F537EBB6179CD89D406DF1C526F04538E4AF2BF9F4.
- S2092 exact missing stack API, EXIT=0/olean yes,
  SHA 81F796480355A5DB529BD6B62425EF1E86C13826D171CEF002A498890985A5FC.

S2092MorphismOfFiniteEtaleStacks remains the exact missing inhabitant.  The
scheme-level cancellation S2091 is actual; the gap is the stack representability
API.  S2090 records that the after-g 2-isomorphism cannot be cancelled to a
before-g presentation, so the presentation route does not give the API.
