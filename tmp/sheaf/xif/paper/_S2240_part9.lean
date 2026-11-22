
/-- **Per-data form of the S2185 strict-cone comparison.**  If the C-presentation has the
full 2-universal property (cone essential surjectivity), the comparison 2-cell of S2185
exists. -/
theorem S2240StrictConeIsoAt
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    (hC : S1852ConeEssSurj (S2130PC f T ptA))
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA)))) := by
  let cPC : (S1852WeakSquare (S2130PC f T ptA)).Cone W := S2240ConePC f g T ptA c
  have h1 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA)))
      (S1852WeakSquare (S2130PC f T ptA)).toX) cPC.toX) :=
    ⟨S2240PhiToSource f g T ptA c⟩
  have h2 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA)))
      (S1852WeakSquare (S2130PC f T ptA)).toY) cPC.toY) :=
    ⟨S2240PhiToProj f g T ptA c⟩
  have h3 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA)))
      (S1852WeakSquare (S2130PC f T ptA)).toX) cPC.toX) :=
    ⟨S2240GraphToSource f g T ptA c⟩
  have h4 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA)))
      (S1852WeakSquare (S2130PC f T ptA)).toY) cPC.toY) :=
    ⟨S2240GraphToProj f g T ptA c⟩
  obtain ⟨e1⟩ := hC W cPC
    (Pseudofunctor.StrongTrans.vcomp
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (S1742StrongTransOfHom (S2130Phi f g T ptA))) h1 h2
  obtain ⟨e2⟩ := hC W cPC
    (Pseudofunctor.StrongTrans.vcomp c.toY
      (S1742StrongTransOfHom (S2130Graph f g T ptA))) h3 h4
  exact ⟨e1.trans e2.symm⟩
