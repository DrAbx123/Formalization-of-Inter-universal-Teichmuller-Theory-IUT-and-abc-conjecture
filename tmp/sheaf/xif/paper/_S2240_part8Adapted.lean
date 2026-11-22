
/-- First comparison, with the scheme map Graph. -/
noncomputable def S2240GraphToSource
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA)))
        (S2130PC f T ptA).toSource)
      (Pseudofunctor.StrongTrans.vcomp c.toX g.map) :=
  (S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA)))
      (Pseudofunctor.StrongTrans.vcomp c.toY (S2130GraphSite f g T ptA))
      (S2130PC f T ptA).toSource
      (S2058WhiskerLeftIso c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA))
        (S2130GraphSite f g T ptA)
        (S2240GraphTransIso f g T ptA))).trans
    (S2240GraphSiteToSource f g T ptA c)

/-- Second comparison, with the scheme map Graph. -/
noncomputable def S2240GraphToProj
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA)))
        (S2130PC f T ptA).projectionMap.transformation)
      c.toY :=
  (S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA)))
      (Pseudofunctor.StrongTrans.vcomp c.toY (S2130GraphSite f g T ptA))
      (S2130PC f T ptA).projectionMap.transformation
      (S2058WhiskerLeftIso c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA))
        (S2130GraphSite f g T ptA)
        (S2240GraphTransIso f g T ptA))).trans
    (S2240GraphSiteToProj f g T ptA c)
