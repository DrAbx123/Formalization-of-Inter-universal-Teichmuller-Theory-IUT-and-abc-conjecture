# S2466/S2467: full mapComp actual; diagram assembly leaves only coherence

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL S2466MapComp (f g : SignGroup) : S2465Map (g*f) ~ S2465Map f >> S2465Map g, assembled by four branch lemmas. EXIT=0, olean 96992, SHA256 0719582503d35f38e4583b3a3e63a359ab7e768c021e0b62a16105e1a41d3008, axioms trio.

S2467DiagramAssemblyAttempt:
- mapId and mapComp compile in LocallyDiscrete.mkPseudofunctor;
- only the three pseudofunctor coherence fields fail (aesop), with explicit goals:
  1. associator: (S2466MapComp (f≫g) h).hom >> ... = eqToHom ...;
  2. left unitor: (S2466MapComp (id) f).hom >> ... = eqToHom ...;
  3. right unitor: (S2466MapComp f id).hom >> ... = eqToHom ... .
- no olean; diagram not actual yet.

Next: prove the three coherence fields by cases on f=1/g=1/h=1 and explicit bicategory/simp, separately. No cF/cK; no fake.