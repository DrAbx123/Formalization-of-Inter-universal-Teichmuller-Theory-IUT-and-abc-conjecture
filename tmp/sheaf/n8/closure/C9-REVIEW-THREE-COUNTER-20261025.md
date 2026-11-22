# C9 review: load-bearing countermodel for `qPilotOutput_mem`

Task: task-468 (Load-bearing countermodel for qPilotOutput_mem). Owner:
volumedet. Date: 2026-10-25. Review + self-contained Lean countermodel.
No edits to `C9Cor312ThreeAssumptions.lean`; only the new Lean file and this
MD were written. No mixed/E3.

## 0. Verdict

`qPilotOutput_mem` is **load-bearing**. The original
`C9Cor312ThreeAssumptions.Theorem311Full` includes the field

    qPilotOutput_mem : qPilotOutput ∈ possibleOutputs

and the proof of `cor312` uses exactly this field to put
`qLog = logVol qPilotOutput` into `R = logVol '' possibleOutputs`.

The new self-contained countermodel shows that all other abstract A1/A2/A3
data can be satisfied while C1 fails, if this field is removed. Therefore
C1 cannot be derived from the remaining A1/A2/A3 data alone; the membership
is an additional compatibility input (xi-e/xi-f content), not a consequence
of Theorem3.11/Prop3.9/Remark3.9.5's other formal fields.

The review accepts the *formal proof* of `cor312` relative to its structure,
but rejects any claim that `qPilotOutput_mem` is supplied by A1-A3 without
that field. The countermodel is abstract/logical, not a source complete-C
counterexample.

## 1. Files and hashes

New Lean file:

    tmp/sheaf/n8/closure/C9ThreeAssumptionsCountermodel.lean
    115 lines, SHA256 3390fc53ee669979d1cadb556e6907d763a016c6a154820acb4b6f5d3a9142e2

Source file (unmodified):

    tmp/sheaf/n8/closure/C9Cor312ThreeAssumptions.lean
    59 lines, SHA256 e71f22d4fdd47faa8de1646713af88bbcd72e2541cd8121824abae131e48f703

Lean compile:

    cd D:\lean
    lake env lean -R D:/lean tmp/sheaf/n8/closure/C9ThreeAssumptionsCountermodel.lean
    EXIT=0

No source Lean was edited.

## 2. What the original proof uses

The source structures:

    Theorem311Full  { Output, possibleOutputs, logVol, qPilotOutput,
                      qPilotOutput_mem }
    Prop39          { qLog, qLog_eq : qLog = logVol qPilotOutput }
    Remark395       { R, R_eq : R = logVol '' possibleOutputs,
                      h, hull_upper : ∀ x∈R, x≤h }
    ThreeAssumptions { T311, P39, R395 }

`cor312` proves `qLog≤h` by:
1. `qLog = logVol qPilotOutput` (Prop39);
2. `qPilotOutput ∈ possibleOutputs` (qPilotOutput_mem);
3. hence `qLog ∈ R` (R_eq);
4. hence `qLog≤h` (hull_upper).

Step 2 is exactly C1's membership. The source docstring labels the field as
'the fixed/coric q-pilot input rigidification is one of them (IPL + final
evaluation map)' — i.e. the field already packages the xi-e/xi-f
compatibility.

## 3. Countermodel without the field

The new file defines:

    Theorem311NoMem  { Output, possibleOutputs, logVol, qPilotOutput }
    Prop39NoMem, Remark395NoMem, ThreeAssumptionsNoMem

and the instance:

    counterT := { Output := Unit, possibleOutputs := ∅,
                  logVol := fun _ => 1, qPilotOutput := () }
    counterP := { qLog := 1, qLog_eq := rfl }
    counterR := { R := ∅, R_eq := by simp [counterT], h := 0,
                  hull_upper := by intro x hx; simp at hx }
    counterA := { T311 := counterT, P39 := counterP, R395 := counterR }

Then:

    counterT_qPilot_not_mem :
      counterT.qPilotOutput ∉ counterT.possibleOutputs
    counterA_C1_false :
      ¬ counterA.P39.qLog ≤ counterA.R395.h

All A1/A2/A3 fields except `qPilotOutput_mem` are satisfied; C1 is false
(1≤0). This is an abstract logical model, not a model of the IUT source.

## 4. Field load-bearing theorem

The file proves:

    C1_of_mem {T} (P : Prop39NoMem T) (R : Remark395NoMem T)
      (hmem : T.qPilotOutput ∈ T.possibleOutputs) : P.qLog ≤ R.h

and

    qPilotOutput_mem_is_load_bearing :
      (¬ counterA.P39.qLog ≤ counterA.R395.h) ∧
      (∀ T P R, T.qPilotOutput ∈ T.possibleOutputs → P.qLog ≤ R.h)

Thus:

- without membership, the remaining fields admit a C1-false model;
- with membership, C1 follows formally.

This is precisely the sense in which the field is load-bearing.

## 5. Consequence for the ThreeAssumptions route

The formal theorem

    A1+A2+A3 => C1

is valid only when A1 includes `qPilotOutput_mem`. The countermodel shows
that the other A1/A2/A3 fields do not imply it. Therefore:

- `qPilotOutput_mem` must be justified from the source (Theorem3.11/xi-e/xi-f)
  or carried as an explicit hypothesis;
- it cannot be silently treated as a consequence of the other abstractions;
- the source's `cor312` is conditional on this membership field, exactly as
  C1 is the open compatibility.

No source counterexample is constructed; the issue is formal
load-bearingness, not a disproof of the source theorem.

## 6. Classification

PROVED (Lean, compile EXIT=0):

- countermodel satisfies all abstract fields except qPilotOutput_mem;
- C1 false in the countermodel;
- qPilotOutput_mem ⇒ C1 formally;
- qPilotOutput_mem is load-bearing.

REVIEW RESULT:

- Original `cor312` is formally correct relative to its structure.
- The structure's membership field is not a consequence of the remaining
  A1/A2/A3 data; it is the C1/xi-e compatibility.
- Any unconditional C1 claim must supply/justify that field.

MISSING: source-level justification of qPilotOutput_mem (xi-e/xi-f),
independent of the field itself.

## 7. Status

Review/countermodel only. No source Lean edits; only the new Lean file and
this MD written. Lean compile EXIT=0. No mixed/E3. `target_accepted=false`;
C1 open without the membership input.
