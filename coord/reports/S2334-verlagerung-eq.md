# S2334: verlagerungOpen_eq exact surface

Layer: O (transfer compatibility).
Source object: verlagerungOpen, transferAb, subgroupOfEquivOfLe.
Domain: composition/transfer naturality in target.
Direction: exact missing; finite-index instance resolved notationally in Prop.

BUILT:
- S2334VerlagerungOpenEqRequired: exact equality with explicit [H.toSubgroup.FiniteIndex].

MINIMAL FAILURE:
- After rw [verlagerungOpen, Verlagerung.transferAb], rfl fails because lift (of_H.comp e).transfer is not definitionally equal to (Ab.map e).comp (lift of.transfer).
- Need transfer_comp/lift_comp lemma: Ab.map e (transfer ϕ x) = transfer (e.comp ϕ) x, or an Abelianization.lift composition lemma.

MISSING exact: S2334VerlagerungOpenEqRequired. No fake.

Lean: tmp/sheaf/xif/paper/S2334VerlagerungEqActual.lean
EXIT=0; SHA256 9EF33F5F31C114E6C4B633345DD7A011CB1B730A8A0518EE2457218337A851F9
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2334VerlagerungEqActual.olean
olean SHA256: 69378C648F641DA8686A03E04CAD7DAF90BC53E1E8594D94273EC646904B3EA9
axioms: none (definition/Prop surface only; no theorem closure).