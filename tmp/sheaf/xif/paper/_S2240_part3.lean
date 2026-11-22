
/-- The comparison of the presentation scheme map S2130Phi with its site form. -/
noncomputable def S2240PhiTransIso
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    Iso (S1742StrongTransOfHom (S2130Phi f g T ptA)) (S2130PhiSite f g T ptA) :=
  S1742StrongTransIsoOfHom (S2130PhiSite f g T ptA)

/-- The comparison of the graph scheme map S2130Graph with its site form. -/
noncomputable def S2240GraphTransIso
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    Iso (S1742StrongTransOfHom (S2130Graph f g T ptA)) (S2130GraphSite f g T ptA) :=
  S1742StrongTransIsoOfHom (S2130GraphSite f g T ptA)

/-- First comparison for Phi, in site form. -/
noncomputable def S2240PhiSiteToSource
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S2130PhiSite f g T ptA))
        (S2130PC f T ptA).toSource)
      (Pseudofunctor.StrongTrans.vcomp c.toX g.map) :=
  (S2058AssociatorIso
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (S2130PhiSite f g T ptA)
      (S2130PC f T ptA).toSource).trans
    ((S2058WhiskerLeftIso
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (Pseudofunctor.StrongTrans.vcomp
        (S2130PhiSite f g T ptA) (S2130PC f T ptA).toSource)
      (Pseudofunctor.StrongTrans.vcomp
        (S2130PB f g T ptA).toSource g.map)
      ((S2130PC f T ptA).isPullback.liftToX (S2240Y (S2130PB f g T ptA).pullbackScheme)
        (S2130PhiCone f g T ptA))).trans
      ((S2058AssociatorIso
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S2130PB f g T ptA).toSource g.map).symm.trans
        (S2058WhiskerRightIso
          (Pseudofunctor.StrongTrans.vcomp
            ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
            (S2130PB f g T ptA).toSource)
          c.toX g.map
          ((S2130PB f g T ptA).isPullback.liftToX W (S2185ConePB f g T ptA c)))))
