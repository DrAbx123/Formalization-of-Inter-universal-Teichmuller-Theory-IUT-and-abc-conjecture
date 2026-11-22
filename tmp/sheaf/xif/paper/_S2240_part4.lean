
/-- Second comparison for Phi, in site form. -/
noncomputable def S2240PhiSiteToProj
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
        (S2130PC f T ptA).projectionMap.transformation)
      c.toY :=
  (S2058AssociatorIso
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (S2130PhiSite f g T ptA)
      (S2130PC f T ptA).projectionMap.transformation).trans
    ((S2058WhiskerLeftIso
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (Pseudofunctor.StrongTrans.vcomp
        (S2130PhiSite f g T ptA) (S2130PC f T ptA).projectionMap.transformation)
      (S2130PhiCone f g T ptA).toY
      ((S2130PC f T ptA).isPullback.liftToY (S2240Y (S2130PB f g T ptA).pullbackScheme)
        (S2130PhiCone f g T ptA))).trans
      ((S2130PB f g T ptA).isPullback.liftToY W (S2185ConePB f g T ptA c)))
