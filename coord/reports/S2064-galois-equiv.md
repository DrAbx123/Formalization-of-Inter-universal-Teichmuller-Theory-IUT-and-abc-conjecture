# S2064: group-level S2047GaloisEquiv actual

Layer: O (S2045/S2046 component (a); actual local completion model).
Source object: Gv v = LocalClosure v ≃ₐ[LocalBase v] LocalClosure v and LocalAbsoluteGalois v.1, via S2063 base/closure equivalences.
Domain: actual local absolute Galois groups.
Direction: group-level conjugacy equivalence, then S2045 orientation.

BUILT:
- S2064BaseEquiv, S2064ClosureEquiv, S2064ClosureEquiv_algebraMap from S2063 actual data.
- S2064ConjRing/S2064ConjRingInv: conjugation by the actual closure equivalence.
- S2064ToLocal/S2064ToGv: conjugation maps preserving the Qp/Base algebra structure (using closure_compat and AlgEquiv.commutes).
- S2064GaloisEquiv : Gv v ≃* LocalAbsoluteGalois v.1.
- S2064S2045GaloisEquiv : S2045GaloisEquiv v = (S2064GaloisEquiv).symm.

PROVED: S2064GaloisEquiv and S2064S2045GaloisEquiv; axioms propext, Classical.choice, Quot.sound only.

MISSING: none for component (a) group level.  Components (b)/(c) remain the S2045/S2046 local-to-PsiCns and local-to-Gau comparisons, to be connected to S2039 actual PsiCns after local CFT port.

Consumer: S2045OperationKummerData component (a), then S2046 component assembly.

Reports read: S2063 source/report; S2047/S2046 sources.

Lean: tmp/sheaf/xif/paper/S2064GaloisEquivActual.lean
EXIT=0; SHA256 0BB5CCF48751AB286BCC27A6882D3A4FC7FE52566063C7A6CFC47C0C4ADA313C
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2064GaloisEquivActual.olean
olean SHA256: 25A473CB6C3B3FA3830EDCA770EE317CAF7A22301009F4713517D8826EAB4BB6
axioms: propext, Classical.choice, Quot.sound (no sorryAx).