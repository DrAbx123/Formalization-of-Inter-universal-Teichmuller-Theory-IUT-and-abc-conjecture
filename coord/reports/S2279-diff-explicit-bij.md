# S2279: explicit-product prod_bij attempt

Layer: O (diff/transfer product).
Source object: S2266DiffExplicit, S2242 identity, Finset.prod_bij.
Domain: explicit diff product reindex.
Direction: exact missing; minimal prod_bij goal recorded.

MINIMAL GOAL after prod_bij:
  ϕ' ⟨(↑(S'.leftQuotientEquiv (φ q0)))⁻¹ * ↑(S'.leftQuotientEquiv (φ q0)), _⟩
  = ϕ ⟨(↑(S.leftQuotientEquiv ((φ).symm (φ q0))))⁻¹ * ..., _⟩
- The right side still contains φ.symm (φ q0) (not simplified).
- rw [hα,hβ] fails because under instances transparency H.map e.toMonoidHom is expected vs H.map (↑e) actual.
- Finset.prod_bij itself was accepted; the block is the per-term subtype/coercion rewrite.

BUILT:
- S2279DiffExplicitBijRequired = S2226DiffTransportRequired.
- S2266_diff_explicit actual from prerequisite.

MISSING exact: per-term rewrite and transported product equality. No fake.

Lean: tmp/sheaf/xif/paper/S2279DiffExplicitBijActual.lean
EXIT=0; SHA256 0E87290C8B9E01E6E0B082C0A52DF79618BD72007136593CCF9F77B7D0910D24
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2279DiffExplicitBijActual.olean
olean SHA256: 84355C6FE0DCF1A5C320BDE386D97B6EB2C98842EAEE2663E188992ECBDA18FF
axioms: none (definition/Prop surface only; no theorem closure).