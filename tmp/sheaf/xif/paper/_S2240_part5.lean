
/-- First comparison for Graph. -/
noncomputable def S2240GraphSiteToSource
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp c.toY (S2130GraphSite f g T ptA))
        (S2130PC f T ptA).toSource)
      (Pseudofunctor.StrongTrans.vcomp c.toX g.map) :=
  (S2058AssociatorIso c.toY (S2130GraphSite f g T ptA)
      (S2130PC f T ptA).toSource).trans
    ((S2058WhiskerLeftIso c.toY
      (Pseudofunctor.StrongTrans.vcomp
        (S2130GraphSite f g T ptA) (S2130PC f T ptA).toSource)
      (S2130PtC f T ptA)
      ((S2130PC f T ptA).isPullback.liftToX (S2240Y T)
        (S2130GraphCone f g T ptA))).trans c.commutes.symm)

/-- Second comparison for Graph. -/
noncomputable def S2240GraphSiteToProj
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp c.toY (S2130GraphSite f g T ptA))
        (S2130PC f T ptA).projectionMap.transformation)
      c.toY :=
  (S2058AssociatorIso c.toY (S2130GraphSite f g T ptA)
      (S2130PC f T ptA).projectionMap.transformation).trans
    ((S2058WhiskerLeftIso c.toY
      (Pseudofunctor.StrongTrans.vcomp
        (S2130GraphSite f g T ptA) (S2130PC f T ptA).projectionMap.transformation)
      (Pseudofunctor.StrongTrans.id (S2240Y T))
      ((S2130PC f T ptA).isPullback.liftToY (S2240Y T)
        (S2130GraphCone f g T ptA))).trans
      (Pseudofunctor.StrongTrans.rightUnitor c.toY))
