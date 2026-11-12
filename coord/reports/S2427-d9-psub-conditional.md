# S2427: conditional Psub NatIso actual; sign projection input exact

Date: 2026-11-02.

Actual:
- S2427Comp T : Q.presheafHom.obj T ≅ S2332Obj T (eqToIso S2271).
- S2427SignProjection : Prop, the exact naturality square for these components.
- S2427NatIso_of_signProjection : S2427SignProjection -> (Q.presheafHom M N ≅ S2332Psub S M N), built by NatIso.ofComponents + ext x.

Axioms: propext, Classical.choice, Quot.sound.

Remaining: prove S2427SignProjection. It is exactly the sign projection/naturality statement; no fake.

Verification:
- EXIT=0
- SHA256: f9b3edd5dd742709abdec227ff312463b8d00f96b12bc199ec00792087ace0c1
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2427PsubNatIsoConditionalActual.olean, size 32576
- axioms: propext, Classical.choice, Quot.sound.