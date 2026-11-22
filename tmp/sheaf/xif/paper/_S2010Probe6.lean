
/-- The split double cover as a scheme over the base. -/
noncomputable abbrev S2010P (T : SchemeOverField S1726K) : SchemeOverField S1726K :=
  Over.mk (S2010Fold T ≫ T.hom)

/-- The projection of the split double cover. -/
noncomputable def S2010Projection (T : SchemeOverField S1726K) :
    S2010P T ⟶ T :=
  Over.homMk (S2010Fold T) rfl

/-- The canonical section of the projection. -/
noncomputable def S2010Section (T : SchemeOverField S1726K) :
    T ⟶ S2010P T :=
  Over.homMk (S2010Inl T) (by
    change S2010Inl T ≫ S2010Fold T ≫ T.hom = T.hom
    rw [← Category.assoc, S2010Inl_fold, Category.id_comp])

/-- The swap sheet automorphism over the base. -/
noncomputable def S2010Swap (T : SchemeOverField S1726K) :
    S2010P T ⟶ S2010P T :=
  Over.homMk (S2010SwapScheme T) (by
    change S2010SwapScheme T ≫ S2010Fold T ≫ T.hom =
      S2010Fold T ≫ T.hom
    rw [← Category.assoc, S2010SwapScheme_fold])

theorem S2010Section_projection (T : SchemeOverField S1726K) :
    S2010Section T ≫ S2010Projection T = 𝟙 T := by
  apply Over.OverMorphism.ext
  exact S2010Inl_fold T

theorem S2010Swap_projection (T : SchemeOverField S1726K) :
    S2010Swap T ≫ S2010Projection T = S2010Projection T := by
  apply Over.OverMorphism.ext
  exact S2010SwapScheme_fold T

/-! ## 2. The uniform enlarged base-change presentation -/

/-- The strong transformation of the fold map. -/
noncomputable abbrev S2010FoldTrans (T : SchemeOverField S1726K) :
    Pseudofunctor.StrongTrans (S1743Y (S2010P T)) (S1743Y T) :=
  S1742StrongTransOfHom (F := S1726K) (S2010Projection T)

/-- The strong transformation of the section. -/
noncomputable abbrev S2010SectionTrans (T : SchemeOverField S1726K) :
    Pseudofunctor.StrongTrans (S1743Y T) (S1743Y (S2010P T)) :=
  S1742StrongTransOfHom (F := S1726K) (S2010Section T)

/-- The strong transformation of the swap. -/
noncomputable abbrev S2010SwapTrans (T : SchemeOverField S1726K) :
    Pseudofunctor.StrongTrans (S1743Y (S2010P T)) (S1743Y (S2010P T)) :=
  S1742StrongTransOfHom (F := S1726K) (S2010Swap T)
