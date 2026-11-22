
/-- The cone over the C-presentation square attached to a cone over the base square. -/
noncomputable def S2240ConePC
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    (S2185PCSquare f g T ptA).Cone W where
  toX := Pseudofunctor.StrongTrans.vcomp c.toX g.map
  toY := c.toY
  commutes :=
    (S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp c.toX g.map)
      (Pseudofunctor.StrongTrans.vcomp c.toY (S2130PtC f T ptA))
      C.map c.commutes).trans
      (S2058AssociatorIso c.toY (S2130PtC f T ptA) C.map)
