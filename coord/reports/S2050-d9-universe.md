# S2050: D9 universe/small-model choice, target-change proposal, exact first missing

Date: 2026-11-02. Status: no actual C_F quotient stack and no actual K-side degree-l cover. Universe obstruction clarified; target-change proposal and exact first missing recorded in Lean. No pointwise groupoid, representable label-only orbicurve, Shrink/ULift, or fake quotient/cover.

## Layer

D9 (C_F/K-side geometric objects), not Cor. 3.12 readout and not S841/S853 lattice.

## Source objects

- C_F: actual S1726 F-line sign action and S1964 quotient target; honest signature (0; [2,2,2]; 1).
- K-side: S1994 actual K-curve/kernel line; paper cover target S1994PaperKSideCover; geometric first field S1994StackyOrbicurveMissing.
- S2029 natural large slice-sheaf model S2029SheafPrestack, values in Cat.{u+1,u+1}.
- Old target: Iut.EtaleStackPseudofunctor K, values in Cat.{u,u}.

## Domain

- C_F: S1726 F-line and its sign action.
- K-side: InitialThetaArithmeticData, SourceSignQuotientData, S1984PaperKCore.
- Universe target: field K : Type u and etale site SchemeOverField K.

## Direction

- Universe choice is a target-shape decision, not an inequality.
- C_F quotient: actual construction of a stack.
- K-side covers: actual degree-l finite-etale cover data.
- Exact first missing is recorded as Prop/structure, no inhabitant.

## BUILT

File: tmp/sheaf/xif/paper/S2050D9UniverseChoiceActual.lean

- S2050OldEtaleStackPseudofunctor = Iut.EtaleStackPseudofunctor K (Cat.{u,u}).
- S2050LargeEtaleStackPseudofunctor K = Pseudofunctor ... Cat.{u+1,u+1}.
- S2050LargeEtaleStackOverField K (large fiber + IsStack field).
- S2050UniverseRoute := keepSmallTarget | raiseToLargeTarget.
- S2050LargeSheafPrestack := S2029SheafPrestack K (actual large-valued object).
- S2050LargeSheafStackMissing := IsStack of that prestack (exact missing).
- S2050LargeSheafSmallModel := Nonempty small model at every test object (exact missing for old target).
- S2050LargeCFData l A: actual large stack over F plus C_F quotient data and honest signature.
- S2050LargeCFFirstMissing l A := Nonempty (S2050LargeCFData l A).
- S2050CFFirstMissing := S1971QuotientStack.
- S2050LargeCFData l A: actual large etale stack over F plus quotient orbicurve, sign-invariant morphism, bicategorical witness, honest signature.
- S2050LargeCFFirstMissing l A := Nonempty (S2050LargeCFData l A).
- s2050LargeCF_toS1964 (def): actual large C_F data gives S1964QuotientStructure.
- S2050KSideFirstMissing := S1994StackyOrbicurveMissing.
- S2050HonestSignature_actual : etthSignature paperCFType = S1964HonestQuotientSignature.

## PROVED

- The natural sheaf prestack is actual and Cat.{u+1,u+1}-valued:
  S2050LargeSheafPrestack, s2050LargeSheafPrestack_obj.
- The honest C_F signature is (0; [2,2,2]; 1), not (1,1)^pm:
  s2050HonestSignature_actual.
- Old target first missing and K-side first missing are named exactly.
- No construction of the quotient stack or K-side cover is asserted.

## MISSING

### Proposal B: raise target to Cat.{u+1,u+1}

1. S2050LargeSheafStackMissing: the slice-sheaf pseudofunctor is an etale stack.
2. S2050LargeCFFirstMissing: actual large C_F data (large stack, quotient orbicurve, sign-invariant morphism, bicategorical witness, honest signature).
3. Full faithfulness / universal property and the comparison with S2022.

### Proposal A: keep Cat.{u,u}

1. S2029SmallModel for every natural large fiber (S2050LargeSheafSmallModel).
2. Pseudofunctorial transport along the small models (not constructed).
3. Then S1971QuotientStack / S1994StackyOrbicurveMissing as before.

### No target change

- C_F: S1971QuotientStack / S1971StackQuotientWitness.
- K-side: S1994StackyOrbicurveMissing, then S1994PaperKSideCoverMissing.
- D9 slot: S1881D9OrbicurveMissing.

## Consumer

- C_F: S1964QuotientStructure -> S1983EtThCF -> D9 slot.
- K-side: S1994PaperKSideCover -> KSideCoverActual -> D9 slot.
- Large route: S2050LargeSheafStackMissing -> S2050LargeCFFirstMissing -> S1964QuotientStructure -> quotient stack.

## Universe recommendation

Choose Proposal B (raise the target universe to Cat.{u+1,u+1}) for the natural sheaf/torsor model, because the actual slice-sheaf prestack already lives there and the old Cat.{u,u} target forces an additional small-model theorem. If the target must remain Cat.{u,u}, Proposal A is the only honest route and the first input is S2029SmallModel plus transport.

This is a target-change proposal, not a completed construction. No Shrink/ULift or pointwise substitution is used.

## O-triangle / q_v attachment

D9 geometric target (C_F quotient, K-side degree-l covers) does not consume the paper O^tri/q_v attachment. That attachment belongs to the multiradial/Kummer log-volume layer, not to the D9 orbicurve geometry. If the paper's D9 readout is later required to carry O^tri/q_v data, the missing input is a separate multiradial/Kummer action, not a lattice or quotient-stack replacement. The actual O^tri object is OtriangleLogVolumeObject; the multiradial action remains missing (GlobalThetaPilotLogKummerCompatibilityActual). D9 must not identify these objects by name.

## Reports read

- coord/MAINLINE_ABC_F.md (especially D6/D9 universe notes)
- coord/reports/S2043-d9-full.md
- tmp/sheaf/xif/paper/S2029GiraudStackificationActual.lean
- S1963, S1964, S1971, S1983, S1989, S1994, S2022 Lean files

## Verification

- Lean file: tmp/sheaf/xif/paper/S2050D9UniverseChoiceActual.lean
- EXIT=0
- SHA256: 3c541d20690a7bde604adc3b845f580d6c7ef3cd08a6c64be70eec73c0242113
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2050D9UniverseChoiceActual.olean, size 215864
- axioms: propext, Classical.choice, Quot.sound; no sorryAx, no new axiom.
