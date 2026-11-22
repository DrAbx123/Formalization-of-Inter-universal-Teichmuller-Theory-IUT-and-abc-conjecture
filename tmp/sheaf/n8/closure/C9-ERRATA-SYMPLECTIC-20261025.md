# C9 errata: symplectic donor corrections (2026-10-25)

Source: task-147/kummer, C9-SYMPLECTIC-SOURCE-20261025.md (314 lines, SHA256 3f98f68a5e143dcd51ed6790b1c839ae7b8811e4e418d48b02e37e7c4d5b9c70).

Corrections to C9-TAME-LOG-DOMAIN-20261025.md §2-§3:

1. rho: Mod(S\{P}) -> Out(G_K) is NOT a group homomorphism (Kondo 2025 Remark 2.18); no splitting/section. The actual donor is the closed preimage H = Phi^{-1}(Sp_{2g}(Z_p)) with Phi(H)=Sp_{2g}(Z_p), not 'image of rho = Sp'.
2. Boundary-word-preserving free-group substitutions are not all actual Galois automorphisms. The actual source is the mapping-class group / Dehn-twist construction, not arbitrary JW boundary substitutions.
3. The 2025 trace basis and 2026 symplectic basis are identified by convention/inference; this is not an explicitly stated cross-paper theorem.
4. Kondo 2025 Theorem 1.3 is for Tr_{k/k^{(d=1)}}; it equals Tr_{K/Q_p} only in the totally ramified C9 local type.
5. J=m, standard-lattice classification, orbit generation, and volume gain ((t-1)/e)log p are inferred consequences, not Kondo theorems.

Status: stage1 natural language only; no Lean. This errata is binding for all follow-up C9 tasks. Original file remains historical; do not use the flawed §2 construction without this correction.
