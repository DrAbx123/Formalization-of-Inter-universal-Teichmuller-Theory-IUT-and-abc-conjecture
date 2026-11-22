# L1-F8 child node — production ThetaLinkSourceCover dependency repair

Status: **stage1 triage record; parent L1-F8 statement node remains unclosed.** This is a child node because the production donor itself does not compile.

Parent: L1-F8 ThetaLinkSourceCover/Slice consumer (`tmp/sheaf/l1-f8/ThetaLinkSourceCoverConsumer.lean`, stage 2 candidate).

## Exact blocker

`lake build LeanFormal.IUT.IUTII.Theta.ThetaLinkSourceCover` → EXIT 1 with three production errors:

1. `LeanFormal/IUT/IUTII/Theta/ThetaLinkSourceCover.lean:295:2: unsolved goals` in `productMap_comp` case `refine_2`; goal
   `(data.snd A ≫ f.hom) ≫ g.hom = data.snd A ≫ (f ≫ g).hom`.
2. `...:413:42: rewrite failed` in `sliceObjectIsoIdentityOfIsIsoHom`; target
   `(asIso (Over.hom object)).hom ≫ (Over.mk (𝟙 Yddot)).hom = Over.hom object`.
3. `...:407:4: failed to compile definition, consider marking it as noncomputable` (uses `asIso`).

The consumer cannot compile because its import olean does not exist; acceptance `lake env lean tmp/sheaf/l1-f8/ThetaLinkSourceCoverConsumer.lean` is blocked at import resolution.

## Ownership

Production file `LeanFormal/IUT/IUTII/Theta/ThetaLinkSourceCover.lean` is not owned by qside under the current SHEAF task ("不要改生产文件"). This child must be assigned to the production file owner.

## Parent file state

`tmp/sheaf/l1-f8/ThetaLinkSourceCoverConsumer.lean` (SHA 458F4E42621AD5AA3E9070BAC564E5DB652D599FDB7426568A91B225CD03B48D, 35 lines) is written exactly per the stage1 record:
- structure fields diagram/root/Yddot/model/data/factorization;
- theorem `thetaLinkSourceCoverConsumer_equivalence` consuming `thetaEquivalence`;
- no sorry.

`statement_compiles`: **no** (import olean missing due donor red).
`proof_body_checked`: **no**.
`kernel_closed` / `target_accepted`: **no**.

## Next executable step

Production owner repairs issues 1–3; then rebuild `LeanFormal.IUT.IUTII.Theta.ThetaLinkSourceCover`, then compile the consumer with `lake env lean -j1`. No change to the consumer statement should be needed if `thetaEquivalence` type stays as recorded.
