
/-- First comparison, with the scheme map Phi. -/
noncomputable def S2240PhiToSource
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        (S2130PC f T ptA).toSource)
      (Pseudofunctor.StrongTrans.vcomp c.toX g.map) :=
  (S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA)))
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S2130PhiSite f g T ptA))
      (S2130PC f T ptA).toSource
      (S2058WhiskerLeftIso
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA))
        (S2130PhiSite f g T ptA)
        (S2240PhiTransIso f g T ptA))).trans
    (S2240PhiSiteToSource f g T ptA c)

/-- Second comparison, with the scheme map Phi. -/
noncomputable def S2240PhiToProj
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        (S2130PC f T ptA).projectionMap.transformation)
      c.toY :=
  (S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA)))
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S2130PhiSite f g T ptA))
      (S2130PC f T ptA).projectionMap.transformation
      (S2058WhiskerLeftIso
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA))
        (S2130PhiSite f g T ptA)
        (S2240PhiTransIso f g T ptA))).trans
    (S2240PhiSiteToProj f g T ptA c)
