# S2305: subgroupOf map coercion exact surface

Layer: O (verlagerungOpen naturality).
Source object: S2300SubgroupOfMapRequired.
Domain: subgroupOf / conjugation equivalence coercion.
Direction: exact missing; minimal goal recorded.

MINIMAL GOAL:
  hy : y ∈ (↑H).subgroupOf ↑K
  target : ↑((S2200ConjEquiv p g K) y) ∈ OpenSubgroup.comap (conj g) H
- Subgroup.mem_subgroupOf.mp hy gives ↑y ∈ H, but the target is membership in an OpenSubgroup.comap, whose coercion/instances differ (OpenSubgroup vs Subgroup, Gv vs LocalAbsoluteGalois).
- simp [S2200ConjEquiv, S2173ConjSubgroupEquiv, S2179MapConjEqComap] makes no progress on the OpenSubgroup.comap target.

BUILT:
- S2305SubgroupOfMapRequired = S2300SubgroupOfMapRequired.

MISSING exact: bridge OpenSubgroup.comap membership to Subgroup.comap and S2200ConjEquiv coercion. No fake.

Lean: tmp/sheaf/xif/paper/S2305SubgroupOfMapActual.lean
EXIT=0; SHA256 CF867FD40D417D3378D02686002214E556A48DC7C723BDD29DA77EF26BB90BD4
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2305SubgroupOfMapActual.olean
olean SHA256: 0DDEC4F5568DA5AB3E810523AA9755FD562A8DCABDBD8D8B8C9725B9528DACB0
axioms: none (definition/Prop surface only; no theorem closure).