# S2215: actual LeftTransversal transport

Layer: O (transfer naturality API).
Source object: H.LeftTransversal, group isomorphism e.
Domain: complements/transversals.
Direction: actual transport S -> e '' S with IsComplement proof.

BUILT:
- S2215TransversalTransport: for e : G ≃* G' and S : H.LeftTransversal, produces (H.map e).LeftTransversal with underlying set e '' S.
- Proof uses Equiv.Set.image, Subgroup.equivMapOfInjective, product equivalence, and e(s*h)=e(s)*e(h).

PROVED: IsComplement transport, axioms trio.

NEXT exact missing: transfer product invariance / diff conjugation naturality, then Abelianization.map(ConjEquiv) vs verlagerungOpen naturality. No fake.

Lean: tmp/sheaf/xif/paper/S2215TransversalTransportActual.lean
EXIT=0; SHA256 FEAEF2E692CF2EDC41BEA36E30EDCD514ADB34D3CDADC1D878528E36E3406E48
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2215TransversalTransportActual.olean
olean SHA256: CCA14C7ECB56D94BA9378E1A21920D0A6EB95041C1DF9C0352DA68A56EA2FCB4
axioms: propext, Classical.choice, Quot.sound (no sorryAx).