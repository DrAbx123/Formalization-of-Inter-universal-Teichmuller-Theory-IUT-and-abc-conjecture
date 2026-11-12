# IUT PREREQUISITES REMAINING (mainline/李维, A321; for Lead A320 assignment)

Status: IUT prerequisite objects NOT complete. Corrected 2.2/2.4 restatements exposed the ALGEBRAIC Qbar layer as named; IUT gate remaining = H6 PARTIAL + deep inputs.
COVERAGE LINE (canonical): 'F=Q component delivered + full-Qbar reduction named (not complete)'.

## Gate rows status (authoritative current)
| Layer | Status | Evidence | Remaining for PASS |
|---|---|---|---|
| L0 curves/function fields | CLOSED/PASS | E1 defs CITABLE; AG01/02 | none |
| L1 divisors/height-weight | CLOSED/PASS | tree asset + AG03 | none |
| L2 cohomology | CLOSED/PASS | AG05 Cech CITABLE; AG_FLT_CechPromotion | none |
| L3 RR/Serde | CLOSED/PASS (ported) | AG_FLT_Promotion/RiemannRoch/CanonicalDivisor/Serde promotions CITABLE; ported assets non-gate | none |
| L4 Belyi/finite maps | PARTIAL | Mzk1 2.1 ALL PROVED; 2.4 F=Q component (base m(S)=0 + rational Belyi existence supported S3236/S3229/S3230/S3237/S3255/S3232); FinMapData resolved | FULL Qbar layer named: (D) finite-Galois PROVED + infinite fixed field class-B + 2.3 Moebius over Qbar/C + AlgebraicNestedInductionInput class-B |
| L5 GenEll | PARTIAL (statement layer citable) | GenEll05 Thm2.1 (i)=>(ii) PROVED; GenEll10b H6 wiring; GenEll15 GeometricCoreAssembly; GenEll16 BelyiExistence; GenEll17 BelyiPair bridge; GenEll13/14 etc. | GenEll Thm2.1 (ii)=>(i) consumer needs noncritical Belyi existence (=> Lemma 2.2 restated target conditional F=Q) + H6 precise GeometricCore; consumer of corrected 2.4 not yet wired |
| L6 AbsTopIII | PARTIAL | 01/03/07/08/09 complete citable; H1-H5/H7 rows closed w/ class-B leftovers; H6 PARTIAL (GenEll transfer; Hull11 upgrade citable; reduction hypotheses named) | H6 precise-ification (assigned 胡尔: Mzk1GeometricCorePreciseActual); AbsTopIII05 deep named input remains |
| L7 EtTh/Theta | PARTIAL | EtTh07/08/09/10/11/12/13 citable; theta power-kernel anti-monotonicity PROVED | realization deeper rows class-B named |
| L8 IUT IV section1 | FROZEN/NOT PASSED | S3171IUTIVSection1{Statement,Estimates,Display,Inputs}+UniformHeightConsumer green; thm110 display conditional on inputs | display/Cor312 assembly requires L0-L7 self-write gaps close + inputs (b) uniform height-vs-volume etc.; remains FROZEN |

## Deep inputs / class-B named (IUT-side)
1. AbsTopIII05 deep construction (paper input; named).
2. H6 GeometricCore: Mzk1GeometricCoreWitness fields free Props (RealStructure:59) - precise-ification required; Hull11/Hull13/GenEll15 consume conditionally.
3. H5 q-side O^x stabilization (class-B named).
4. H7/Ob9 arbitrary-iterate bound (deep class-B; Hull12 one-sided only).
5. EtTh/theta realization deeper rows (class-B named).
6. IUT IV section1 inputs: (b) uniform height-vs-volume / region-relative-to-hull-and-weight etc. (L8 frozen until L0-L7 close).

## Corrected 2.2/2.4 algebraic layer (named; NOT complete)
- Layer R (F=Q): DELIVERED component (rational base m(S)=0 + rational Belyi existence; conditional assembly skeleton).
- Layer A (Qbar, paper 2.4 lines 144-160, proof 163-206): named inputs: AlgebraicClosureFixedFieldPaperInput (infinite Galois fixed field; class-B), AlgebraicNestedInductionInput (paper 179-206 m/d descent step; class-B NEW), BetaAvoidingBelyiBaseInput (class-B; blocked - no beta control in TauCeti Belyification; qpilot searching upstream/port), CorrectedStepProviderPaperInput, CorrectedAssemblyPaperInput.
- 2.3 Moebius separation over Qbar/C: Q-typed Möbius lib + C-typed variant delivered (S3253/S3256); separation PROVED (S3237) at rational/measure level; Qbar application wiring NOT built.
- Measures m/d: meaningful only for algebraic points; rational-only m(S)=0 trivial (base case).

## Immediate assignment queue (matching Lead A320)
- 胡尔: H6 precise-ification Mzk1GeometricCorePreciseActual (precise GeometricCoreStatement + reduce free Prop fields; consume GenEll15/Hull11/Hull13).
- 齐波: search upstream/ported beta-avoiding Belyi existence (to unlock BetaAvoidingBelyiBaseInput class-B) + C-typed CV integration.
- 拉蒂: gate table corrected-scope draft (base-only rational rows; named Qbar reduction rows; coverage line verbatim).
- 司徒: conditional 2.2 induction (Mzk1Lemma22InductionProofActual hbase/hstep/CPointCVInImageStatement -> InductionStatement -> target_of_induction) + item(i) via BelyiCvBridge declarations.
- 艾比: conditional 2.4 base provider (Mzk1Lemma24BaseProviderRestatedActual with BetaAvoidingBelyiBaseInput -> Target) + assembly conditional chain + Layer A AlgebraicNestedInductionInput statement file.
- 史蒂: scope notes + consumer LAST; wire Qbar layer only after named layers available.
- 谢德/拉蒂: audit + xref updates; no closure claims.

## Rules
- GATE NOT PASSED; binding HOLD; FINAL ROWS suspended; no closure claims under rational-only scope.
- Any coverage statement must use: 'F=Q component delivered + full-Qbar reduction named (not complete)'.
- Pins: registry 14041 / gate in flux / record 18800; L8 frozen; no registry edits.