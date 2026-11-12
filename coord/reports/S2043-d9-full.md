# S2043: D9 full object audit — C_F quotient stack, K-side covers, exact first missing

Date: 2026-11-02. Status: audit + exact first-missing Lean package. No actual quotient stack or K-side cover is constructed. No fake quotient/cover, no pointwise-groupoid substitution, no representable-stack substitution, no label-only orbicurve as the l-tors object.

## 0. Reports and files read

- `coord/MAINLINE_ABC_F.md`
- `coord/reports/gap-exploration-20261030.md`
- `coord/reports/S1449-report-ABC-graph.md`
- `coord/ACTUAL-OBLIGATIONS-CLASSIFICATION.md`
- `tmp/sheaf/xif/paper/S1963SignActionAssemblyActual.lean`
- `tmp/sheaf/xif/paper/S1964QuotientCFActual.lean`
- `tmp/sheaf/xif/paper/S1971ActionStackificationActual.lean`
- `tmp/sheaf/xif/paper/S1983EtThSignatureBridgeActual.lean`
- `tmp/sheaf/xif/paper/S1989KSideCoverActual.lean`
- `tmp/sheaf/xif/paper/S1991HonestTargetAliasesActual.lean`
- `tmp/sheaf/xif/paper/S1994KSideCoversActual.lean`
- `tmp/sheaf/xif/paper/S2022QuotientStackActual.lean`
- `tmp/sheaf/s1984/S1984KSideObjectAudit.lean`
- `tmp/sheaf/xif/paper/S1881D9D7bActual.lean`

The requested `coord/reports/S2043-d9-full.md` did not exist before this report.

## 1. Layer and source objects

**Layer:** D9 (D7b/D8 frontier) — C_F/K-side geometric objects for IUT I Definition 3.1(b),(d),(f). It is not the Cor. 3.12 log-volume comparison and not a Route C lattice statement.

**Source objects:**

- F-side line `S1726Orbicurve` and actual sign action `Iut.OrbicurveSignAction S1726Orbicurve` (S1963/S1964).
- F-side quotient target `C_F = [X_F / {±1}]`:
  - quotient structure `S1964QuotientStructure`;
  - honest signature target `S1964HonestQuotientSignature = (0; [2,2,2]; 1)`;
  - [EtTh] honest target `S1983EtThCF` / `S1983FirstMissing`;
  - functorial stack quotient missing `S1971QuotientStack` / `S1971StackQuotientWitness`.
- K-side:
  - actual K-side punctured elliptic curve and kernel line (S1994);
  - paper cover target `S1994PaperKSideCover` / `S1994PaperKSideCoverMissing`;
  - geometric first field `S1994StackyOrbicurveMissing`.
- D9 slot `S1881D9OrbicurveSlot` / `S1881D9OrbicurveMissing`.
- Root-stack donor `S2022QuotientStackPackage` for `[Z / mu_l]`; this is **not** `[X_F/{±1}]`.

**Domains:**

- C_F quotient: the actual S1726 F-line/sign action and its S1964/S1971 F-side orbicurve quotient data.
- K-side covers: production `InitialThetaArithmeticData`, `SourceSignQuotientData`, paper K-core `S1984PaperKCore`, clause C/D data.
- D9 slot: `S1732A l` line, C_F/C_K/X_K signatures and covers.
- Root stack S2022: `K` field and `l : PrimeGeFive`, with `Z = Spec K[t]/t^l`, `mu_l`.

**Direction / target kind:**

- C_F/K-side: actual construction of a quotient stack / degree-l cover, plus honest signature data; not an inequality.
- `S2022FirstMissing`: existence of a quotient-stack package for `[Z/mu_l]`, not an inequality.
- D9 slot: actual object tuple (`cF, core, cK, xK, coverMap, groups`).

## 2. What is actually built/proved

### C_F side

- S1964:
  - actual involution `S1964Neg`, fixed-point classification, three two-torsion points;
  - honest signature `S1964HonestQuotientSignature = (0; [2,2,2]; 1)`, hyperbolic, Euler characteristic `-1/2`;
  - proof that the honest signature is not the paper label `(1,1)^pm`;
  - proof that the signature label is not determined by the stack fiber;
  - `S1964QuotientStructure` (quotient orbicurve, sign-invariant morphism, bicategorical universal property) and its exact first missing `S1964FirstMissing`.
- S1971:
  - pointwise quotient groupoid `S1971PointwiseQuotient` and its automorphism/nontrivial-aut checks;
  - exact first missing `S1971QuotientStack` = functorial pointwise colimit + etale stack condition;
  - first missing step `S1971FirstMissingStep` = functorial pointwise colimit;
  - `S1971StackQuotientWitness` and actual consumer `toS1964`;
  - theorem `S1964FirstMissing_ofStackQuotientWitness`.
- S1983/S1964:
  - `paperCF_signature : etthSignature paperCFType = S1964HonestQuotientSignature`;
  - `S1983FirstMissing_iff_honest`;
  - `S1964FirstMissing_ofS1983`;
  - honest target is `S1983EtThCF` (quotient + honest label), not the S1881 `(1,1)^pm` label alone.

### K-side

- S1994:
  - actual K-side punctured curve `S1994KCurve`;
  - actual rank-one quotient/kernel line from clause C, `S1994KernelLine_card = l`;
  - exact missing quotient curve/isogeny and cover; no Mathlib isogeny quotient theory;
  - `S1994PaperKSideCoverMissing` and `S1994StackyOrbicurveMissing`;
  - machine-checked obstruction: representable orbicurves have no nontrivial automorphisms at any point, hence no order-l stacky point;
  - label-only representable orbicurve exists with the `(1,l-tors)` signature but no order-l automorphism — so the label does not force the geometry.
- S1989:
  - cover records `KSideCoverActual`, finite-etale degree-l fields;
  - exact missing and vacuity of its label fields;
  - no inhabitant of the paper cover.
- S2022:
  - pointwise quotient data for `[Z/mu_l]`, twist/torsor comparison, quotient-stack package;
  - exact missing `S2022FirstMissing`;
  - this is a **root-stack donor for the K-side l-tors geometry**, not C_F.

### D9 slot

- S1881:
  - `S1881D9OrbicurveSlot` exact structure;
  - `S1881D9OrbicurveMissing` exact;
  - `S1881D9OrbicurveSlot.firstField : S1881CF l` with label `sourceTypeOneOnePlusMinus`;
  - S1983/S1964 show that this label is not the honest quotient signature `(0;[2,2,2];1)`.

## 3. What is missing

### C_F quotient stack

The pointwise action groupoid is insufficient. The first missing is:

```lean
S1971QuotientStack : Prop
```

and the stronger witness form:

```lean
Nonempty (S1971StackQuotientWitness l A)
```

Both are exact; no inhabitant is asserted. The honest target additionally requires:

```lean
S1983FirstMissing l A
```

which is equivalent to `Nonempty (S1964HonestCFQuotient l A)`. The signature label `(1,1)^pm` cannot substitute for the honest signature; S1964 proves the label is not determined by the stack fiber.

### K-side degree-l covers

The first missing is:

```lean
S1994StackyOrbicurveMissing l A
```

i.e. an actual K-side orbicurve with an order-l stacky point, and then the full record:

```lean
S1994PaperKSideCoverMissing l A S C
```

with actual `X_K^->`, `C_K^->`, degree-l finite-etale covers, quotient square, and honest stacky orders `l`, `2`, `l`. The root-stack package `S2022FirstMissing` is a possible donor but does not itself produce the C_K/X_K geometry.

### D9 slot

```lean
S1881D9OrbicurveMissing l
```

is exact. C_F first field is `S1881CF l`; the S1881 label is `sourceTypeOneOnePlusMinus`, which is not the honest S1964 signature.

## 4. No-go / forbidden substitutions

- Pointwise action groupoid cannot stand for the quotient stack (S1971 distinguishes functorial colimit and stack condition).
- S2022 pointwise `[Z/mu_l]` is not `[X_F/{±1}]`; it is a K-side root-stack donor.
- Representable or label-only orbicurve cannot stand for the l-tors orbicurve: S1994 proves no nontrivial automorphism and no order-l stacky point.
- The S1881/S1989 paper labels do not imply geometry; S1994 label-vacuity and S1964 fiber-label independence are machine-checked.
- No fake cover, no arbitrary quotient, no `True`/`Nonempty` substitution for the geometric objects.

## 5. S2043 Lean package

File: `tmp/sheaf/xif/paper/S2043D9FullActual.lean`

Declarations:

- `S2043CFQuotientStackFirstMissing := S1971QuotientStack`;
- `S2043CFStackWitnessFirstMissing l A := Nonempty (S1971StackQuotientWitness l A)`;
- `S2043CFHonestFirstMissing l A := S1983FirstMissing l A`;
- `S2043KSideFirstMissing l A := S1994StackyOrbicurveMissing l A`;
- `S2043KSideCoverFirstMissing := S1994PaperKSideCoverMissing`;
- `S2043D9SlotFirstMissing l := S1881D9OrbicurveMissing l`;
- `S2043paperCF_signature : etthSignature paperCFType = S1964HonestQuotientSignature`;
- `S2043S1964Quotient_of_stackWitness`;
- `S2043S1964Quotient_of_honestMissing`;
- `S2043KSideStacky_of_coverMissing`.

Verification:

- `EXIT=0`;
- SHA256: `543f74af4fc360d85a642f315ab0e6793d563b5c48503c0e861c139b7114a6f9`;
- olean: `D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2043D9FullActual.olean`, size 21376;
- axiom footprint: `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, no new axiom.

## 6. First milestone decision

Neither actual C_F quotient stack nor K-side cover is constructed. The first milestone is therefore **exact first missing**, in dependency order:

1. C_F stack quotient: `S1971QuotientStack` / `S1971StackQuotientWitness`.
2. K-side stacky orbicurve: `S1994StackyOrbicurveMissing`; then full `S1994PaperKSideCoverMissing`.
3. D9 slot: `S1881D9OrbicurveMissing`.

Routing recommendation: attack C_F `S1971StackQuotientWitness` by constructing the functorial pointwise colimit and etale stackification; keep S2022 as root-stack donor only for K-side. Do not use S841/S853 or Cor. 3.12 lattice/readout objects for D9.

## 7. Consumer chain

- C_F: `S1964QuotientStructure` → `S1983EtThCF` → D9 `S1881D9OrbicurveSlot.cF`.
- K-side: `S1994PaperKSideCover` → `KSideCoverActual` → S1881 `cK/xK/coverMap`.
- Root stack: `S2022QuotientStackPackage` → `S1994StackyOrbicurveMissing` (geometry donor only).

No consumer is replaced by a pointwise groupoid or a label-only orbicurve.
