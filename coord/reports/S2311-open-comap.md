# S2311: OpenSubgroup.comap membership bridge actual

Layer: O (verlagerungOpen naturality coercion).
Source object: OpenSubgroup.comap membership.
Domain: open subgroup comap coercion.
Direction: bridge actual; S2300 subgroupOf equality remains.

BUILT:
- S2311_mem_comap_toSubgroup: x ∈ ↑(H.comap f hf) ↔ f x ∈ H.
- S2311SubgroupOfMapRequired = S2300SubgroupOfMapRequired.

PROVED: bridge; axioms [propext].

MINIMAL REMAINING GOAL:
- target ↑((S2200ConjEquiv p g K) y) ∈ S2169ConjIndex p g H; after change/rw the membership is open-subgroup membership but S2169ConjIndex must be unfolded to OpenSubgroup.comap before OpenSubgroup.mem_comap applies.
- symm coercion of S2200ConjEquiv needs subgroupMap/subgroupCongr coercion simplification.

MISSING exact: S2311SubgroupOfMapRequired. No fake.

Lean: tmp/sheaf/xif/paper/S2311OpenComapActual.lean
EXIT=0; SHA256 F9C19956AF8FBD348C9E12307730282F43798C50B5057410297C90EE2FBFE6F4
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2311OpenComapActual.olean
olean SHA256: ABE056FE856E93980F451C29EC7AA765C01901B69C0E6093ED2667D819C352BE
axioms: propext (bridge only); exact Props no closure.