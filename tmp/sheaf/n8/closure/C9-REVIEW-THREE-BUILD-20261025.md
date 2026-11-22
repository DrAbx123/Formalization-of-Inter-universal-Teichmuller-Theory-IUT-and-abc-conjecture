# C9 independent Lean build/axiom audit: C9Cor312ThreeAssumptions

Task: task-463 (C9-REVIEW-THREE-BUILD-20261025). Owner: logdescent. Date: 2026-10-25. Independent build/axiom audit only; no source edits; only named deliverable written. No mixed/E3. target_accepted=false; P6 open.

## 0. Verdict

The Lean file builds independently in a clean temp directory, with EXIT 0, zero sorry, and no hidden sorryAx or extra axiom beyond sourceThreeAssumptions + the standard Lean/Mathlib axioms. The exact axiom audit is:

    cor312:
      [propext, Classical.choice, Quot.sound]
    cor312_unconditional:
      [propext, Classical.choice, Quot.sound, sourceThreeAssumptions]
    sourceThreeAssumptions:
      [propext, Classical.choice, Quot.sound, sourceThreeAssumptions]

The build is kernel-clean relative to its stated axiom.

However, the semantic audit finds that sourceThreeAssumptions is not just "Theorem 3.11 + Prop 3.9 + Remark 3.9.5" as needed for an actual Cor3.12 proof: its Theorem311Full structure contains the field

    qPilotOutput_mem : qPilotOutput in possibleOutputs,

which is exactly the q-pilot-as-possible-output membership C1. The theorem cor312 uses this field. Thus the build validates the conditional theorem

    ThreeAssumptions (including C1 membership) => qLog <= h,

not Cor3.12 from A1-A3 alone. The axiom audit passes; the target audit does not.

## 1. Source and environment

Source file: tmp/sheaf/n8/closure/C9Cor312ThreeAssumptions.lean
- SHA256: E71F22D4FDD47FAA8DE1646713AF88BBCD72E2541CD8121824ABAE131E48F703
- lines: 59
- sorry occurrences: 0
- imports: Mathlib.Data.Real.Basic, Mathlib.Data.Set.Basic, Mathlib.Tactic
- no C9/local imports.

Lean: version 4.32.2, x86_64-w64-windows-gnu, commit f3b06c705e6c85f5314019d5d3baab0fec5b580c, Release.
Project: D:\lean, lake-manifest mathlib rev 905b95818eb32af7874a58b427f50c1711a5e96c (inputRev v4.32.2).

Build procedure:
1. Created clean temp directory D:\lean\tmp\review-three-build-20261025.
2. Copied the source file there; copy SHA256 identical to source.
3. Built the copy with the serial wrapper:
     pwsh -NoProfile -File D:\lean\tmp\n8-20261018\lead\lean-serial.ps1 env lean -j1 -R D:/lean D:\lean\tmp\review-three-build-20261025\C9Cor312ThreeAssumptions.lean
4. Built an audit copy of the same declarations with extra #print axioms lines for cor312, cor312_unconditional, sourceThreeAssumptions.
5. Source file was not edited; its hash after the audit is unchanged.
The temp copies are audit artifacts, not deliverables; only this file is written as the task deliverable.

## 2. Build result

Command: lean -j1 -R D:/lean on the clean copy.
- EXIT: 0
- stderr: empty
- stdout (normal build, source's own #print axioms):
    'LeanFormal.IUT.N8Closure.C9Cor312ThreeAssumptions.cor312_unconditional' depends on axioms: [propext,
     Classical.choice,
     Quot.sound,
     sourceThreeAssumptions]
- no errors, no warnings, no sorryAx.

The audit copy additionally gave:
    cor312 depends on [propext, Classical.choice, Quot.sound]
    cor312_unconditional depends on [propext, Classical.choice, Quot.sound, sourceThreeAssumptions]
    sourceThreeAssumptions depends on [propext, Classical.choice, Quot.sound, sourceThreeAssumptions]

## 3. Exact declaration/dependency audit

Declarations in the file:
- structure Theorem311Full: Output, possibleOutputs, logVol, qPilotOutput, qPilotOutput_mem.
- structure Prop39 (T): qLog, qLog_eq.
- structure Remark395 (T): R, R_eq, h, hull_upper.
- structure ThreeAssumptions: T311, P39, R395.
- theorem cor312 (A : ThreeAssumptions) : A.P39.qLog <= A.R395.h.
- axiom sourceThreeAssumptions : ThreeAssumptions.
- theorem cor312_unconditional : sourceThreeAssumptions.P39.qLog <= sourceThreeAssumptions.R395.h.

Dependency of cor312:
- only the standard three axioms [propext, Classical.choice, Quot.sound];
- no dependence on sourceThreeAssumptions because it is a theorem over an arbitrary A;
- proof uses A.R395.R_eq, A.P39.qLog_eq, A.T311.qPilotOutput_mem, A.R395.hull_upper.

Dependency of cor312_unconditional:
- standard three plus sourceThreeAssumptions;
- no other axiom.

#print axioms sourceThreeAssumptions lists itself plus the standard three; this is expected for a declared axiom.

There is no sorryAx, no Classical.choice beyond the standard allowed axioms, and no local/extra axiom.

## 4. Semantic dependency: the axiom package contains C1

sourceThreeAssumptions is an axiom of type ThreeAssumptions. Its T311 : Theorem311Full field includes:

    qPilotOutput : Output
    qPilotOutput_mem : qPilotOutput in possibleOutputs

The theorem cor312 proves qLog is in R by rewriting R = logVol '' possibleOutputs and using qPilotOutput_mem; then hull_upper gives qLog <= h.

This means:
- the "Theorem311Full" field is not merely the statement that the algorithm has possible outputs; it asserts that the q-pilot output is one of them;
- that assertion is exactly C1/q-pilot-as-output membership (the compatibility at issue in LANA 9.2/xi-e-xi-f);
- the axiom package therefore assumes C1 rather than deriving it from A1-A3.

So the build is a valid proof of:

    (ThreeAssumptions including qPilotOutput_mem) => qLog <= h,

but it is not an unconditional proof of Cor3.12 from the three source assumptions in the sense of A1=Theorem3.11, A2=Prop3.9, A3=Remark3.9.5 alone. The difference is precisely the C1 membership field.

## 5. What is and is not established by this build

Established:
- the Lean file compiles independently (EXIT 0);
- zero sorry;
- theorem cor312 is kernel-checked with only standard axioms;
- cor312_unconditional is kernel-checked relative to sourceThreeAssumptions + standard axioms;
- the exact dependency is as printed above.

Not established:
- that sourceThreeAssumptions is a source theorem (it is an axiom);
- that the qPilotOutput_mem field follows from A1/A2/A3;
- an unconditional Cor3.12 or C1;
- any target/comparator acceptance for P6.

## 6. Classification

| Item | Status |
|---|---|
| independent clean build | PASS (EXIT 0) |
| sorry count | 0 |
| hidden extra axiom | NONE beyond sourceThreeAssumptions + standard |
| cor312 axiom set | [propext, Classical.choice, Quot.sound] |
| cor312_unconditional axiom set | standard + sourceThreeAssumptions |
| sourceThreeAssumptions semantic content | includes qPilotOutput_mem = C1 membership |
| Cor3.12 from A1-A3 alone | NOT established by this file |
| statement_compiles | true |
| proof_body_checked | true (declarations compiled) |
| kernel_closed | true relative to sourceThreeAssumptions |
| target_accepted | false |

## 7. Conclusion

The independent build/axiom audit passes mechanically: the file builds cleanly, has no sorry, and cor312_unconditional depends only on the standard three axioms plus the single declared axiom sourceThreeAssumptions. There is no extra axiom.

But the axiom package is not the intended three-source-assumption package: its Theorem311Full includes qPilotOutput_mem, i.e. the q-pilot-as-possible-output membership C1. The Lean theorem therefore proves the inequality conditional on C1; it does not derive C1 from Theorem3.11/Prop3.9/Remark3.9.5. The build validates the conditional implication, not Cor3.12 unconditionally.

No source Lean edits; no mixed/E3; no arbitrary data. Only this deliverable file written. target_accepted=false; P6 open.
