# S2455: full mapComp' app identity — endpoint mismatch, residual goal

Date: 2026-11-02. Serialized lake env lean -j1 only.

ACTUAL (from S2453):
  ((S2152PFunctor.toPseudofunctor'.mapComp' f g h hh).hom.toNatTrans.app M).1
    = 𝟙 ((S2152PFunctor.toPseudofunctor'.map h).toFunctor.obj M).fst
EXIT=0, olean 54080, SHA256 7668353c..., axioms ok.

ATTEMPT: strengthen to whole app identity:
  ((...mapComp' f g h hh).hom.toNatTrans.app M) = 𝟙 ((...map h).toFunctor.obj M)

Failed: the two endpoints are definitionally different:
  source: (S2152PFunctor.map h).toFunctor.obj M
  target of app: (S2152PFunctor.map f ≫ S2152PFunctor.map g).toFunctor.obj M
so the RHS 𝟙 at the source object has the wrong target. cases/subst on hh does not reduce the composite object syntactically.

EXACT RESIDUAL: prove either
  HEq (app M) (𝟙 ((S2152PFunctor.map h).toFunctor.obj M))
or the eqToHom-shape
  app M = (eqToIso (S2152PFunctor.map_comp f g)).hom.toNatTrans.app M
then use Functor.ext/Cat.Hom.ext to get identity functor and map_apply.

No general S2427SignProjection, no IsStack claim, no fake.

Files:
- S2455AppIdentityActual.lean: EXIT!=0, no olean, source SHA256 40b9e765f692fd1bd49211a20269490e92a4b88aafa854dc3519ad05231220ff.
- S2453MapCompIdProofActual.lean: EXIT=0, olean 54080.