
/-- `inl` then `fold` is an isomorphism of transformations. -/
noncomputable def S2010SectionFoldIso (T : SchemeOverField S1726K) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2010SectionTrans T) (S2010FoldTrans T))
      (Pseudofunctor.StrongTrans.id (S1743Y T)) :=
  (S1844YComp (S2010Section T) (S2010Projection T)).trans
    ((eqToIso (congrArg (S1742StrongTransOfHom (F := S1726K))
      (S2010Section_projection T))).trans (S1844YId T))
