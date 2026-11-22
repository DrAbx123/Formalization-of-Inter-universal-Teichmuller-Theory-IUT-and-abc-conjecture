# FINAL_DEPENDENCY_AUDIT

Audit target: LeanFormal.IUT.XiFPaper.PaperXiFFinalActual.paperLevelXiF_actual

## 1. Kernel axiom audit

Command run:

  cd D:\lean
  lake env lean -j1 -R 'D:\lean' 'tmp\sheaf\xif\paper\FinalAxiomAuditActual.lean'

Exit code: 0

Exact #print axioms output:

  'LeanFormal.IUT.XiFPaper.PaperXiFFinalActual.paperLevelXiF_actual'
    depends on axioms: [propext, Classical.choice, Quot.sound]

  'LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.globalQPilotLog_le_globalThetaHullLog'
    depends on axioms: [propext, Classical.choice, Quot.sound]

Additional probe (tmp/final_dep_probe.lean) also gave:

  perBQPilotLog_le_perBThetaHullLog
    depends on axioms: [propext, Classical.choice, Quot.sound]

  actualPaperXiFTarget
    depends on axioms: [propext, Classical.choice, Quot.sound]

No sorryAx, no additional axiom, no PUnit/True dependency appears in the
kernel axiom list.

## 2. Final theorem signature

Exact #check:

  paperLevelXiF_actual {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData l) :
    PaperLevelXiFTargetActual.ActualPaperXiFTarget T

There is no extra Fintype, MeasurableSpace, BorelSpace, Haar, or other
typeclass parameter in the final theorem signature. Only T is an input.

Exact #print shows the final proof term is:

  fun {l} T => actualPaperXiFTarget T

## 3. Actual construction of the local instances

PaperXiFFinalActual supplies the instances used internally, not as hypotheses:

- Fintype (Bad (nativePlaceSelection T)):
  local instance nativeBadFintypeInstance :=
    NativeBadFintypeForTActual.nativeBadFintype T

  NativeBadFintypeForTActual.nativeBadFintype is
  Classical.choice of nativeBadFintype_nonempty, whose proof uses the actual
  finite bad-reduction set and actual local disjointness.

- MeasurableSpace on each qVFamTensorBlock T b:
  qVFamCanonicalMeasurableSpace T b := borel (qVFamTensorBlock T b)

- BorelSpace on each qVFamTensorBlock T b:
  qVFamCanonicalBorelSpace T b := ⟨rfl⟩

Thus the typeclass inputs appearing inside the bridge/proof modules are
instantiated by actual constructions in the final file, not required from the
caller.

## 4. Grep of the direct final proof path

Direct files checked:

- PaperXiFFinalActual.lean
- PaperLevelXiFTargetBridgeActual.lean
- PaperLevelXiFTargetProofActual.lean
- PaperLevelXiFTargetActual.lean
- RootNormalizedContainmentActual.lean
- RootHullMeasureActual.lean
- RootHullContainmentInequalityActual.lean
- QVFamNormalizedGeneratorSupplyActual.lean
- QVFamRootFactorCorrectionActual.lean
- QVPilotThetaHullNestingActual.lean
- SignedLabelOneActual.lean
- VbadPlaceIndexingActual.lean
- NativeBadFintypeForTActual.lean

Result: no code-level sorry, admit, custom axiom, PUnit, True, toy, or
value-layer surrogate in these files. The only matches are docstrings that
explicitly say no such object is used.

## 5. Broader import closure

The full transitive import closure of PaperXiFFinalActual.lean contains 353
local files. A grep of that closure finds legacy textual hits, including:

- tmp/sheaf/n8/closure/NativeC3.lean:185: sorry
- SourceDefinition31Boundary.lean: selectedWitness_spec : True
  and badWitness_spec : True
- SourceDefinition31RootLemmas.lean: stage_d5_kernel_status : True
  through stage_d11_kernel_status : True
- Places.lean: finite/infinite predicates returning True
- several Example36 / PrimeStrip effective := fun _ => True
- several docstring occurrences of the words toy, surrogate, value-layer

These are imported source files, not proofs used by the final theorem. The
kernel check in Section 1 shows no sorryAx or extra axiom in the final theorem
dependency. The exact final proof term is the one-line unfolding above and the
bridge theorem term printed by #print; it uses the actual scalar comparison
proof and the actual root normalized containment, not the legacy True/sorry
declarations.

Residual audit risk: a textual grep of the whole import closure cannot by
itself prove that no unused legacy declaration is referenced, because Lean
imports whole modules. The kernel axiom check and the explicit proof-term
inspection are the decisive evidence for this theorem.

## 6. Verdict

1. Axioms: only propext, Classical.choice, Quot.sound. PASS.
2. No sorry/admit/extra axiom in the kernel dependency. PASS.
3. Final theorem has no extra Fintype/Measurable/Borel/Haar inputs; those are
   supplied by actual local instances. PASS.
4. Broader import closure contains legacy True/sorry text in unused modules;
   this is not part of the final theorem kernel dependency, but it is recorded
   as residual repository hygiene, not as a failed final axiom check.
5. The final theorem remains a scalar target:
   ActualPaperXiFTarget T, derived via actual per-b root-normalized containment
   and monotonicity, not via LGP/Kummer/Ind compatibility or a carrier
   equivalence.

## 7. Evidence files

- tmp/final_dep_probe.out: exact #print axioms and #check output.
- tmp/final_dep_probe2.out: exact #print proof terms for actualPaperXiFTarget
  and its scalar bridges.
- tmp/sheaf/xif/paper/FinalAxiomAuditActual.lean: kernel axiom probe.
