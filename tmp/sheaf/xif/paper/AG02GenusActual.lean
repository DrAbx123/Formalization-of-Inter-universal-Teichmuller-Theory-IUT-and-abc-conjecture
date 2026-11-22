import tmp.sheaf.xif.paper.AG01CurveFoundationsActual

/-!
# AG-02: genus interface for the curve layer (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: [Mzk1] GeometricCore build,
coord/AG-INFRA-PLAN.md.

Mathlib has no curve genus (AG-00 audit: missing).  This file records the
minimal HONEST interface: genus is carried as explicit data attached to a curve,
not asserted by an axiom or computed by a fake definition.  The replacement plan
(AG-INFRA-PLAN layer 4) is: once coherent cohomology and differentials exist,
genus := finrank_k H^0(X, Omega^1_{X/k}); the exact target statement is
S3133GenusCohomologyTarget below (a named target, not proved here).
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.AG02GenusActual

universe u

/-- Genus data attached to a curve: a natural number (interface layer; to be
replaced by the cohomological definition once the cohomology layer exists). -/
structure S3133GenusInterface {k : Type u} [Field k]
    (C : LeanFormal.IUT.XiFPaper.AG01CurveFoundationsActual.S3133CurveOver k) where
  /-- the genus value -/
  genus : Nat

/-- The genus read off from the interface data. -/
def S3133Genus {k : Type u} [Field k]
    {C : LeanFormal.IUT.XiFPaper.AG01CurveFoundationsActual.S3133CurveOver k}
    (G : S3133GenusInterface C) : Nat :=
  G.genus

/-- The genus read off from the interface is the interface value (rfl). -/
theorem S3133Genus_eq {k : Type u} [Field k]
    {C : LeanFormal.IUT.XiFPaper.AG01CurveFoundationsActual.S3133CurveOver k}
    (G : S3133GenusInterface C) :
    S3133Genus G = G.genus :=
  rfl

/-- Named target for the cohomological genus (layer 4 of the plan): once the
cohomology layer exists, the interface genus is to be identified with
finrank_k H^0(X, Omega^1_{X/k}).  This is a target statement, not asserted. -/
def S3133GenusCohomologyTarget {k : Type u} [Field k]
    (C : LeanFormal.IUT.XiFPaper.AG01CurveFoundationsActual.S3133CurveOver k)
    (G : S3133GenusInterface C) (genusCohomology : Nat) : Prop :=
  G.genus = genusCohomology

end LeanFormal.IUT.XiFPaper.AG02GenusActual
