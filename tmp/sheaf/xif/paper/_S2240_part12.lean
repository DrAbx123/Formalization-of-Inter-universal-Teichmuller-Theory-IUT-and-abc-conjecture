
/-! ## The per-cover form: fixed target cover, coherence from a strong structure -/

/-- The cone essential surjectivity of the C-presentations, at a fixed target cover. -/
def S2240ConeEssSurjAt (B C : S1728Cover) : Prop :=
  forall (A : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber),
    S1852ConeEssSurj (S2130PC f T ptA)

/-- The S2185 strict-cone comparison, at a fixed target cover. -/
def S2240ConeIsoAt (B C : S1728Cover) : Prop :=
  forall (A : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    (W : EtaleStackPseudofunctor S1726K)
    (c : (S2130BaseSquare f g T ptA).Cone W),
    Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA))))

/-- The comparison at a fixed target cover from its presentation coherence. -/
theorem S2240ConeIsoAt_of_coneEssSurjAt (B C : S1728Cover)
    (h : S2240ConeEssSurjAt B C) : S2240ConeIsoAt B C :=
  fun A f g T ptA W c => S2240StrictConeIsoAt f g T ptA (h A f g T ptA) c

section Family

variable {B C : S1728Cover}

/-- The strict cone over the S2185 strict square, from the comparison at a fixed target
cover. -/
noncomputable def S2240StrictCone (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    (S2185StrictSquare f g T ptA).Cone W where
  toX := (S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c)
  toY := c.toY
  commutes := (h A f g T ptA W c).some

/-- The S1911 witness of the strict square (independent of the comparison). -/
noncomputable def S2240StrictWitness
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    (S2185StrictSquare f g T ptA).TwoPullbackWitness :=
  S1911Witness (sq := S2185StrictSquare f g T ptA)
    (pX := S2130P_fst f g T ptA) (pY := S2130P_snd f g T ptA)
    (by
      simpa only [S1911BaseF, S1911BaseG,
        S1742HomOfStrongTrans_strongTransOfHom] using
        S2185P_isPullback f g T ptA)
    rfl rfl

/-- The lift of a cone into the strict apex. -/
noncomputable def S2240Lift (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    (W : EtaleStackPseudofunctor S1726K)
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Pseudofunctor.StrongTrans W (S2240Y (S2130P f g T ptA)) :=
  (S2240StrictWitness f g T ptA).lift W (S2240StrictCone h f g T ptA c)

/-- The comparison of the lift with the source leg. -/
noncomputable def S2240LiftToX (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S2240Lift h f g T ptA W c)
        (S2130ToSource f g T ptA)) c.toX :=
  (S2058AssociatorIso (S2240Lift h f g T ptA W c)
    (S1742StrongTransOfHom (S2130P_fst f g T ptA))
    (S2130PB f g T ptA).toSource).symm.trans
    ((S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp (S2240Lift h f g T ptA W c)
        (S1742StrongTransOfHom (S2130P_fst f g T ptA)))
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (S2130PB f g T ptA).toSource
      ((S2240StrictWitness f g T ptA).liftToX W
        (S2240StrictCone h f g T ptA c))).trans
      ((S2130PB f g T ptA).isPullback.liftToX W (S2185ConePB f g T ptA c)))

/-- The comparison of the lift with the test leg. -/
noncomputable def S2240LiftToY (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S2240Lift h f g T ptA W c)
        (S2130Proj f g T ptA)) c.toY :=
  (S2240StrictWitness f g T ptA).liftToY W (S2240StrictCone h f g T ptA c)

end Family