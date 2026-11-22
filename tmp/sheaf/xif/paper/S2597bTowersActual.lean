import tmp.sheaf.xif.paper.S2596zTPrimeBatch1Actual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2597bTowersActual

abbrev Cb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev Sb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S
abbrev Fb : Type := LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual.S1720Field
abbrev Lb : Type := LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057FiveDivisionField
abbrev OLb : Type := LeanFormal.IUT.XiFPaper.S2594LP0PActual.OL
abbrev Tb : Type := LeanFormal.IUT.XiFPaper.S2594LP0PActual.T
abbrev Tb' : Type := LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.T'

lemma algMap_Cb_Fb_Lb (x : Cb) :
    algebraMap Cb Lb x = algebraMap Fb Lb (algebraMap Cb Fb x) := rfl

lemma algMap_Cb_OLb_Lb (x : Cb) :
    algebraMap Cb Lb x = algebraMap OLb Lb (algebraMap Cb OLb x) := rfl

/-! ## The algebra C -> T' -/

noncomputable def gCT' : Cb →+* Tb' :=
  (algebraMap OLb Tb').comp (algebraMap Cb OLb)

noncomputable instance instAlgCT' : Algebra Cb Tb' := gCT'.toAlgebra

lemma gCT'_apply (x : Cb) :
    gCT' x = algebraMap OLb Tb' (algebraMap Cb OLb x) := rfl

lemma Cden_mem_MT :
    algebraMap Cb OLb (LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden : Cb) ∈
      LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.MT := by
  rw [← LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.hMT]
  exact Submonoid.mem_powers _

lemma gCT'_Cden_unit : IsUnit (gCT' (LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden : Cb)) := by
  rw [gCT'_apply]
  exact IsLocalization.map_units Tb' ⟨_, Cden_mem_MT⟩

lemma gCT'_unit : ∀ y ∈ Algebra.algebraMapSubmonoid Cb
    (Submonoid.powers (LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.c : ℤ)),
    IsUnit (gCT' y) := by
  intro y hy
  obtain ⟨m, hm, rfl⟩ := hy
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff m
    (LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.c : ℤ)).mp hm
  have hc : algebraMap ℤ Cb (LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.c) =
      (LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden : Cb) := rfl
  rw [map_pow, map_pow, hc]
  exact IsUnit.pow n gCT'_Cden_unit

/-! ## The algebra S -> T' -/

noncomputable def liftST' : Sb →+* Tb' :=
  IsLocalization.lift (M := Algebra.algebraMapSubmonoid Cb
      (Submonoid.powers (LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.c : ℤ)))
    (g := gCT') (fun y => gCT'_unit y.1 y.2)

noncomputable instance instAlgSbTb' : Algebra Sb Tb' := liftST'.toAlgebra

lemma liftST'_comp :
    liftST'.comp (algebraMap Cb Sb) = gCT' :=
  IsLocalization.lift_comp (M := Algebra.algebraMapSubmonoid Cb
    (Submonoid.powers (LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.c : ℤ)))
    (fun y => gCT'_unit y.1 y.2)

noncomputable instance instIsLocT' :
    IsLocalization (Algebra.algebraMapSubmonoid OLb
      (Submonoid.powers (LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden : Cb))) Tb' := by
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  rw [LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.hMT]
  infer_instance

/-! ## The algebra S -> L (through F) -/

noncomputable def gSL : Sb →+* Lb :=
  (algebraMap Fb Lb).comp (algebraMap Sb Fb)

noncomputable instance instAlgSbLb : Algebra Sb Lb := gSL.toAlgebra

lemma gSL_apply (x : Sb) : gSL x = algebraMap Fb Lb (algebraMap Sb Fb x) := rfl

/-! ## The MT-localization instance on T -/

noncomputable instance instIsLocMTT :
    IsLocalization LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.MT Tb := by
  rw [← LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.hMT]
  infer_instance

lemma eTT'_algebraMap (x : OLb) :
    LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT' (algebraMap OLb Tb x) =
      algebraMap OLb Tb' x := by
  have h := (IsLocalization.algEquiv LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.MT Tb Tb').commutes x
  simpa [LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'] using h

lemma eTT'_symm_algebraMap (x : OLb) :
    LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'.symm (algebraMap OLb Tb' x) =
      algebraMap OLb Tb x := by
  have h := (IsLocalization.algEquiv LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.MT Tb Tb').symm.commutes x
  simpa [LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'] using h

/-! ## Compatibility of the two localization maps C -> T -/

lemma liftST_comp :
    LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftST.comp (algebraMap Cb Sb) =
      LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gCT :=
  IsLocalization.lift_comp (M := Algebra.algebraMapSubmonoid Cb
    (Submonoid.powers (LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.c : ℤ)))
    (fun y => LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gCT_unit y.1 y.2)

lemma liftTL_algebraMap (y : OLb) :
    LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftTL (algebraMap OLb Tb y) =
      algebraMap OLb Lb y :=
  IsLocalization.lift_eq (M := Submonoid.powers (algebraMap Cb OLb
      (LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden : Cb)))
    (g := algebraMap OLb Lb)
    (fun y => LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gOL_unit y.1 y.2) y

/-! ## Algebra-map compatibility for the six towers -/

lemma algMap_Cb_OLb_Lb_comp :
    algebraMap Cb Lb = (algebraMap OLb Lb).comp (algebraMap Cb OLb) := by
  ext x
  exact algMap_Cb_OLb_Lb x

lemma algMap_OLb_Tb'_Lb_comp :
    algebraMap OLb Lb = (algebraMap Tb' Lb).comp (algebraMap OLb Tb') := by
  ext x
  change algebraMap OLb Lb x =
    LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftTL
      (LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.eTT'.symm (algebraMap OLb Tb' x))
  rw [eTT'_symm_algebraMap, liftTL_algebraMap]

lemma algMap_Cb_OLb_Tb'_comp :
    algebraMap Cb Tb' = (algebraMap OLb Tb').comp (algebraMap Cb OLb) := rfl

lemma algMap_Cb_Sb_Tb'_comp :
    algebraMap Cb Tb' = (algebraMap Sb Tb').comp (algebraMap Cb Sb) := by
  rw [show algebraMap Sb Tb' = liftST' from rfl, liftST'_comp]
  rfl

lemma algMap_Cb_Sb_Lb_comp :
    algebraMap Cb Lb = (algebraMap Sb Lb).comp (algebraMap Cb Sb) := by
  ext x
  rw [show algebraMap Sb Lb = gSL from rfl]
  simp only [RingHom.comp_apply, gSL]
  rw [show algebraMap Sb Fb (algebraMap Cb Sb x) = algebraMap Cb Fb x from
    RingHom.congr_fun LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.liftCL_comp x]
  exact (algMap_Cb_Fb_Lb x).symm

lemma algMap_Sb_Tb'_Lb_comp :
    algebraMap Sb Lb = (algebraMap Tb' Lb).comp (algebraMap Sb Tb') := by
  apply IsLocalization.ringHom_ext (M := Algebra.algebraMapSubmonoid Cb
    (Submonoid.powers (LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.c : ℤ)))
  ext x
  simp only [RingHom.comp_apply]
  rw [show algebraMap Sb Tb' (algebraMap Cb Sb x) = gCT' x from
    RingHom.congr_fun liftST'_comp x]
  rw [show gCT' x = algebraMap OLb Tb' (algebraMap Cb OLb x) from rfl]
  have h3 : algebraMap Tb' Lb (algebraMap OLb Tb' (algebraMap Cb OLb x)) =
      algebraMap OLb Lb (algebraMap Cb OLb x) := by
    simpa only [RingHom.comp_apply] using
      (RingHom.congr_fun algMap_OLb_Tb'_Lb_comp (algebraMap Cb OLb x)).symm
  rw [h3]
  have h1 : algebraMap Sb Lb (algebraMap Cb Sb x) = algebraMap Cb Lb x := by
    simpa only [RingHom.comp_apply] using (RingHom.congr_fun algMap_Cb_Sb_Lb_comp x).symm
  rw [h1]
  exact algMap_Cb_OLb_Lb x

lemma algMap_Sb_Fb_Lb_comp :
    algebraMap Sb Lb = (algebraMap Fb Lb).comp (algebraMap Sb Fb) := rfl

theorem liftTL_comp_liftST :
    LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftTL.comp
        LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftST = algebraMap Sb Lb := by
  apply IsLocalization.ringHom_ext (M := Algebra.algebraMapSubmonoid Cb
    (Submonoid.powers (LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.c : ℤ)))
  ext x
  simp only [RingHom.comp_apply]
  rw [show LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftST (algebraMap Cb Sb x) =
    LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gCT x from
    RingHom.congr_fun liftST_comp x]
  rw [show LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gCT x =
    algebraMap OLb Tb (algebraMap Cb OLb x) from rfl]
  rw [liftTL_algebraMap]
  have h1 : algebraMap Sb Lb (algebraMap Cb Sb x) = algebraMap Cb Lb x := by
    simpa only [RingHom.comp_apply] using (RingHom.congr_fun algMap_Cb_Sb_Lb_comp x).symm
  rw [h1]
  exact (algMap_Cb_OLb_Lb x).symm

#print axioms algMap_Cb_OLb_Lb_comp
#print axioms algMap_OLb_Tb'_Lb_comp
#print axioms algMap_Cb_Sb_Tb'_comp
#print axioms algMap_Cb_Sb_Lb_comp
#print axioms algMap_Sb_Tb'_Lb_comp
#print axioms liftTL_comp_liftST

end LeanFormal.IUT.XiFPaper.S2597bTowersActual
end
