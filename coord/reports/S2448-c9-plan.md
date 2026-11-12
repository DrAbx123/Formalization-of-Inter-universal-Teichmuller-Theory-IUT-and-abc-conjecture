# S2448 — C9 general normalization + xi-f proof plan (BUILD HOLD, no compilation)

Date: 2026-11-03. Status: planning only. No Lean file was compiled for this plan.
Build incident hold is active: no `lake env lean` / `lake build` commands until
build coordinator clearance.

## 0. Already actual (accepted before hold)

- S2441C9PaperCarrierActual.lean, EXIT=0, SHA256
  `58B0AF92BFEF79F05D9FE1ED06EA909D33FACAB8E14B3248AC9475E33D45B919`.
  - `S2441PaperQPilotCarrier`: fixed-Type piloted strip, actual q_v generators,
    Def 3.8(i) divisor, `paperQPilotDivisor` equality.
  - `S2441PilotedT5Binding`: `sourceQPilotStrip (S1895PaperO D).boundary` anchor,
    reduced strip, generator-compatible piloted identification.
  - `s2441_concrete_normalization`:
    `sourceQPilotSignedLog (paperInput D).initial =
      -((S1487Cand.order : Real) * Real.log 5)`.
  - `s2441_concrete_divisor_deg`:
    `deg (paperQPilotDivisor D) = (S1487Cand.order : Real) * Real.log 5`.
- S2422/S2440 chain: actual-prime units, Kummer index iff S2135, C1 projection
  conditional on `S2404QPilotArithmeticRequired`; exact missing xi-f readout.

Axioms probe for S2441 v2 new declarations was blocked by transient Mathlib
`.olean.private` read errors before the hold; must be rerun after clearance.

## 1. General normalization: target statement

For a concrete `D : S1895PaperInput`, define the paper-normalized scalar
skeleton (subject to proof of the arithmetic lemmas):

```lean
noncomputable def paperRootFactor (l : PrimeGeFive) : Real :=
  (2 * (l.value : Real))⁻¹

noncomputable def paperNormalizedMagnitude (D : S1895PaperInput) : Real :=
  (Module.finrank ℚ (PaperFmod D) : Real)⁻¹ *
    ∑ b : (paperInput D).initial.badPlaces,
      (paperQVOrder D b : Real) * IUTIVPlace.weight (PaperFmod D)
        (IUTIVPlace.finite (paperBadBasePlace D b))

noncomputable def paperNormalizedSignedLog (D : S1895PaperInput) : Real :=
  - paperRootFactor D.l * paperNormalizedMagnitude D
```

Target actual theorem (to be proved or replaced by exact counterexample):

```lean
theorem paperNormalizedSignedLog_eq_source (D : S1895PaperInput) :
    paperNormalizedSignedLog D =
      sourceQPilotSignedLog (paperInput D).initial
```

Fallback if the concrete model shows a mismatch: prove the corrected formula
and record `S2441QPilotPaperNormalizationRequired` as the general exact missing.

## 2. qParameter ↔ q_v and badPlaces ↔ V_bad

Existing actual data:
- `paperQV D b = (paperInput D).initial.reduction.qParameter b` is rfl
  (S1968 `paperQV_eq_qParameter`).
- `paperQVOrder D b` is the actual completed-DVR order of the q candidate;
  `paperQVOrder_abs_log`: `|Real.log (paperQV D b)| =
    (paperQVOrder D b : Real) * Real.log 5`.
- `paperBadBasePlace D b = b.1.maximalIdeal` is the actual base Fmod prime.
- `paperBadBasePlace_weight`: `IUTIVPlace.weight ... = Real.log 5`.

Plan for the general mapping structure (actual for S1895):

```lean
structure S2448BadPlaceMap (D : S1895PaperInput) where
  place : (paperInput D).initial.badPlaces →
    HeightOneSpectrum (NumberField.RingOfIntegers (PaperFmod D))
  place_eq : ∀ b, place b = paperBadBasePlace D b
  q_v : (paperInput D).initial.badPlaces → Real
  q_v_eq_qParameter : ∀ b, q_v b = paperQV D b
  order : (paperInput D).initial.badPlaces → Nat
  order_eq : ∀ b, order b = paperQVOrder D b
  residueWeight : (paperInput D).initial.badPlaces → Real
  residueWeight_eq : ∀ b, residueWeight b = Real.log 5
```

Proof steps:
1. Destructure/inspect `S1895PaperInput` to expose
   `(paperInput D).initial.badPlaces = Bad (S1280Selection D.l)` definitionally.
2. Use `S1280Bad_subsingleton D.l` for the concrete singleton bad family;
   `S1527Bad0 D.l` is the unique bad place.
3. `paperQV_eq_qParameter` and `paperQVOrder_abs_log` supply the q_v/order
   identification; `paperBadBasePlace_weight` supplies log 5.
4. Record `S2448GeneralVbadMapRequired` if a source-generic
   `SourceDefinition31Data.badPlaces → V_bad` map is required; current tree has
   no separate V_bad type.

## 3. 1/(2l), 1/[F:Q], local residue weights

### 3.1 Root factor 1/(2l)

Source: IUT-IV p. 23 (iut4.txt L1383-L1388):
`|log(q)| = (1/(2l)) log(q)`, with `log(q) := deg(q^□_ADiv)`.
IUT-I Ex. 3.2(iv) (iut1.txt L3774-L3785): `q^{[2u]} = q^{[1u] 1/(2l)}`.

Plan:
```lean
def paperRootFactor (l : PrimeGeFive) : Real := (2 * (l.value : Real))⁻¹

theorem paperRootFactor_mul_two_l (l) :
    paperRootFactor l * (2 * (l.value : Real)) = 1
```

For the concrete S1895 model, `paperQVOrder` is already the completed-DVR
order of the q candidate; the audit flags that S1968 uses unnormalized
`IUTIVArithmeticDivisor.deg`.  Before claiming equality with the paper scalar,
prove one of:
- (A) the concrete order already absorbs the 2l root factor, so
  `2*l*order_C3 = order_C3` is false unless order_C3 is a q^{[2u]} order;
- (B) the correct normalized scalar is `-(1/(2l))*deg`, giving a factor
  `(2l)⁻¹` mismatch with `sourceQPilotSignedLog`.

Decide A/B by proving `paperQVOrder_eq_orderC3` and comparing with the S1527
definition of q_v.  If B, record `S2441QPilotPaperNormalizationRequired` and
prove a concrete mismatch theorem.

### 3.2 Normalized degree 1/[F:Q]

Source: IUT-IV Def 1.9(i), pp. 21-22 (iut4.txt L1234-L1257):
`deg := (1/[F:Q]) * deg_F`, `deg_F` weight `log(#k_v)`.
Tree: `IUTIVArithmeticDivisor.deg` is unnormalized `deg_F`
(`ArithmeticDivisorDegree.lean` L108-L119); `ndeg` exists L128-L137.

Plan:
```lean
theorem paperFmod_finrank_two (D : S1895PaperInput) :
    Module.finrank ℚ (PaperFmod D) = 2
```
Proof route: `GaussianField = AdjoinRoot (X^2 + 1)`; use
`AdjoinRoot.powerBasis` (nonzero polynomial) and `PowerBasis.finrank`, then
`natDegree_X_pow_sub_C`/`natDegree` computation.  The old probe looked for
`AdjoinRoot.finrank` (not present) — use `AdjoinRoot.powerBasis` and
`Module.finrank_eq_card_basis` or `PowerBasis.finrank`.

Then define:
```lean
def paperNormalizedDegree (D) : Real :=
  (Module.finrank ℚ (PaperFmod D) : Real)⁻¹ *
    IUTIVArithmeticDivisor.deg (F := PaperFmod D) (paperQPilotDivisor D)
```
and prove `deg = [F:Q] * normalizedDegree`.

### 3.3 Local residue weights

Source: Rem 3.1.1(ii) pp.94-95 (L5315-L5371);
Rem 2.4.2(ii) p.89 (L5042-L5066); Prop 3.9(i) pp.115-116 (L6724-L6778).
Tree: `ProcessionNormalizationWeightsActual.lean` defines
`localNormalizedWeight = 1/[K_w:(F_mod)_v]` and
`processionAverage` over `F_l^x`; `VbadPlaceIndexingObstruction` is unproved.

Plan:
```lean
structure S2448LocalWeightRequired (D) where
  localWeight : (paperInput D).initial.badPlaces → Real
  localWeight_eq : ∀ b, localWeight b =
    (1 : Real) / ((paperInput D).arithmetic.K ?).finrank ...
  weightedSum : Real
  weightedSum_eq : weightedSum =
    ∑ b, localWeight b * (paperQVOrder D b : Real) * Real.log 5
```

Actual work: for S1895 concrete, `paperBadBasePlace_weight = log 5` and
`[F:Q]=2`; the K/F local degree is the Gaussian residue degree 2.  Prove
`localWeight b = (2)⁻¹` and the weighted sum equals the normalized degree.
If the K/F local degree API is insufficient, record
`S2448LocalResidueWeightRequired` with no inhabitant.

## 4. Prop 3.9(i) procession average

Source: Prop 3.9(i) pp.115-116; Rem 3.9.3 pp.119-120.
Tree: `ProcessionNormalizationWeightsActual.processionAverage` and
`localNormalizedWeight` exist; no attachment to `sourceQPilotSignedLog`.

Plan:
1. Instantiate the procession data for the concrete S1895 capsule family.
2. Prove the diagonal q-pilot image case: the average of a constant q-pilot
   log-volume is that constant (existing `average_const`-style lemma).
3. State the general averaged scalar:
```lean
noncomputable def paperProcessionQPilotLogVolume (D) : Real :=
  processionAverage (capsuleFamily D) (fun _ => paperQPilotLogVolume D)

theorem paperProcessionQPilotLogVolume_eq_diagonal (D) :
    paperProcessionQPilotLogVolume D = paperQPilotLogVolume D
```
4. If the capsule family/weights are not constructible, record
`S2448ProcessionAverageRequired` with the exact average type and no inhabitant.

## 5. Literal O^▷(A) pro-generators

Source: IUT-II Def 4.9(vii)-(viii); IUT-III Def 3.8(i) p.112 L6506-L6544.
Tree: S1979 `PilotedFTimesMuPrimeStrip` has a scalar `generator` at each bad
place; its docstring says the literal
`O^▷(A) ⊆ O^◃(A)` at a universal-covering pro-object with `rho_v` is missing.

Exact missing structure (no inhabitant):
```lean
structure S2448LiteralOProGeneratorRequired (D : S1895PaperInput) where
  proObject : Type
  proMonoid : proObject → Type
  submonoid : ∀ x, Set (proMonoid x)
  generator : ∀ b, proMonoid (proObjectAt D b)
  generator_mem : ∀ b, generator b ∈ submonoid (proObjectAt D b)
  rho : ∀ b, proMonoid (proObjectAt D b) → Real
  rho_eq_log : ∀ b, rho (generator b) = Real.log (paperQV D b)
```

The actual construction requires:
1. a universal-covering pro-object of the bad-place split Frobenioid;
2. the literal `O^▷(A)` submonoid;
3. `rho_v` realified value maps;
4. the comparison with S1979's scalar generator layer.

If no API, `S2448LiteralOProGeneratorRequired` remains exact missing; do not
identify the scalar generator with the literal monoid generator.

## 6. xi-f paper family P_C, nu_C, coverage

Source: IUT-III Cor 3.12 pp.173-174 (L10152-L10180); Step (xi-d)
pp.183 (L10661-L10667); (xi-e) pp.183-184 (L10682-L10704); (xi-f)
p.184 (L10705-L10715); C9-XIF-R-DEFINITION-AUDIT; S1447; S2362.

Target interface (fixed C):
```lean
structure S2448PaperOutputFamily (R : SourceTheorem311Realization ...) where
  P_C : Set (ActualOutput R)
  P_C_nonempty : P_C.Nonempty
  nu_C : ActualOutput R → Real
  Q_C : Real
  Q_C_eq : Q_C = paperQPilotLogVolume C
  upper : ∀ D ∈ P_C, nu_C D ≤ -|log Θ|
  coverage_exact : ∃ D ∈ P_C, nu_C D = Q_C
  -- OR:
  coverage_signed : ∀ ε > 0, ∃ D ∈ P_C, Q_C - ε ≤ nu_C D
  readout_eq : ∀ D ∈ P_C, nu_C D = profile.logVolume D.source
```

Proof plan:
1. Reuse S1447 `S1447SignedCoverage` / `S1447OutputReadoutProjection`;
   prove exact/signed coverage + uniform upper bound ⇒ `Q_C ≤ H_C`
   (S1447 consumer, C9XiESourceConditionLogic).
2. The current `BridgeOutput.possibleOutputs` is the singleton `{b.out}`;
   it is explicitly not the paper family.  Do NOT use it as P_C.
3. Need actual paper family of Theorem 3.11 output data in the 1-column, modulo
   Ind1-3; not present.  Record `S2448PaperOutputFamilyRequired` with no
   inhabitant if it cannot be constructed.
4. If a family is constructed, connect `nu_C` to S2362 `profile.logVolume`
   and S2404 arithmetic identity; derive `Q_C ≤ signedHullLogVolume` and
   `H_C < top`.
5. Exact pointwise equality `profile.logVolume(D) = -|log q|` is stronger than
   the paper inequality; keep it separate from coverage and label it as the
   S2404/S2396 input, not as paper xi-f.

## 7. File/dependency plan after build clearance

New independent files:
- `tmp/sheaf/xif/paper/S2448GeneralNormalizationActual.lean`
  (maps/weights/root factor/F:Q; actual lemmas + exact missing structures).
- `tmp/sheaf/xif/paper/S2448ProcessionAverageActual.lean`
  (Prop 3.9(i) average; actual diagonal lemma or missing).
- `tmp/sheaf/xif/paper/S2448LiteralOProGeneratorActual.lean`
  (literal O^▷ pro-generator interface; expected exact missing).
- `tmp/sheaf/xif/paper/S2448XiFCoverageActual.lean`
  (paper family/coverage; exact or missing).

Integration:
- S2441 carrier/T5 binding stays the actual base.
- S2442/S2362 chain consumes only actual LHS; xi-f coverage remains explicit
  missing until constructed.
- No file may turn a missing structure into an assumed field for an actual
  theorem.

## 8. Acceptance criteria

For each file:
- `EXIT=0`; olean exists; SHA256 recorded; `#print axioms` for every new
  declaration; no `sorry`/`admit`/custom axiom.
- Actual theorem: statement uses only constructed objects (no missing
  structure as hypothesis).
- Missing result: named structure/Prop with no inhabitant, exact fields, and
  source citations; not a theorem that assumes it.

Known risk: Mathlib artifact incident hold; all `lake` commands resume only
after build coordinator clearance.
