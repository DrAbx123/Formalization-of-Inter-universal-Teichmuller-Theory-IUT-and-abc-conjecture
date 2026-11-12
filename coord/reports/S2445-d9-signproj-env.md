# S2445: sign projection special case not validated; Mathlib olean build broken

Date: 2026-11-02.

Attempted theorem:
  S2445_signProjection_id (x : Q.presheafHom.obj T) :
    (S2427Comp T).hom (Q.presheafHom.map (1 : T) x) = S2332Psub.map (1 : T) ((S2427Comp T).hom x)

Compile attempts FAILED before elaborating the file because Mathlib build artifacts are missing:
- Mathlib/Tactic/Widget/LibraryRewrite.olean
- Mathlib/MeasureTheory/Integral/Bochner/Set.olean.private
- Mathlib/Topology/Algebra/UniformField.olean
EXIT != 0; no olean produced. These errors are environment/build-artifact failures, not Lean proof errors; likely caused by concurrent subagent builds.

No actual sign projection lemma is claimed. The source is queued for recompilation when Mathlib artifacts are restored.

Exact goal remains S2427SignProjection:
  forall T1 T2 p x, (S2427Comp T2).hom (Q.map p x) = Psub.map p ((S2427Comp T1).hom x).

No fake, no IsStack claim.

Verification:
- Lean EXIT: failed (missing Mathlib oleans)
- SHA256 source: 240d5ca2de3cfe5ca7d6a7f0266411a7c9cf9ca1c88e83d71d2e594319e2be44
- olean: absent