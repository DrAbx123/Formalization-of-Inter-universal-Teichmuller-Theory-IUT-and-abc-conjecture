# S2368: root-set Galois transport

Date: 2026-11-03. Layer O; consumer S2352/S2342/S2217.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2368RootGaloisDoneActual.lean
  SHA256 D2EEC5CFD1A3ACFB10AB6132CD9CDFC29E73B01A94F570803FBEA091F21B22B1
  EXIT=0
  olean SHA256 437401001E4A40DA488599443E7999A45C9AB10773193B611B357BCDFA7035AB
  size 74480
  axioms propext, Classical.choice, Quot.sound.

Theorems:

- s2368_algebraMap_smul:
    algebraMap O_L L (sigma • a) = sigma (algebraMap O_L L a),
  using S2361SmulActual.s2361_algebraMap_smul;
- s2368_rootTransport:
    ((s2345RootSetEquiv f hmonic).symm
      (rootPerm K L f hsplit sigma
        ((s2345RootSetEquiv f hmonic) a))).1 = sigma • a.1,
  using apply_symm_apply, s2345RootSetEquiv_apply, the rfl rootPerm action,
  and S2361 algebraMap compatibility.

K and L are declared at Type (not Type*) because S2167 rootPerm fixes Type.

## Exact first missing: arithFrobAt reduction

Target:

  Ideal.Quotient.mk P (sigma • a) =
    frobBar p P (Ideal.Quotient.mk P a)

for H : IsArithFrobAt (O_K) sigma P.

Two formal blockers:

1. The type IsArithFrobAt (O_K) sigma P requires

     SMulCommClass Gal(L/K) (O_K) (O_L),

   which is not synthesized by the current local O_L MulSemiringAction instance.
   Need a local instance or a proof that O_K acts compatibly with Gal(L/K).

2. `frobBar` is in namespace
     LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual;
   needs opening for the residue-side unfold.

Once available, the proof should be:

  have h := AlgHom.IsArithFrobAt.mk_apply H a;
  rw [frobBar];
  rw [Ideal.over_def P p];
  exact h.

## Next after arithFrobAt

- transport this reduction through redRootEquiv to rootPerm;
- factor multiset identification;
- S2217Missing.

## Conclusion

- BUILT: ambient algebraMap compatibility and O_L-root -> rootPerm transport.
- MISSING: SMulCommClass Gal O_K O_L instance, then arithFrobAt reduction.
- no fake; no false S2057 data.
