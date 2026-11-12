# S2445: Cech minimal definitions and exact amalgamation interface actual

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL definitions:
- S2445CechNerve S R : Type 1 := R.category.
- S2445DescentDatum S R : Type 1 := (S2029SheafPrestack K).DescentData (fun g : R.category => g.obj.hom).
- S2445AmalgamationRequirement S R := forall D, Nonempty (Amalgam (S2029SheafPrestack K) ... D).
- S2445AllCechAmalgamation := forall S R hR, S2445AmalgamationRequirement S R.
- S2445AllCechAmalgamation_iff : S2134EffDescentOnEtaleFamilies K ↔ S2445AllCechAmalgamation (actual, from S2134 iff).

EXIT=0, olean 21080, SHA256 5eb5c5c52e3d3fd2e10069a54c18d43890982a6c97a00743b4412e7d474a2696, axioms propext/Classical.choice/Quot.sound.

No inhabitant of S2445AmalgamationRequirement/S2445AllCechAmalgamation. Mathlib v4.32.2 has DescentData/IsStackFor/Amalgam, but no general Cech descent/amalgamation for sheaves on etale slices. Base cases remain identity/maximal/split-epi (S2134).

No IsStack claim, no fake.