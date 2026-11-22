import tmp.sheaf.xif.paper.EtTh11ThetaRealizationRowsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section

/-!
# STEP 0 prior-art: mod-l projection factorization|level divisibility|QuotientGroup.map|power kernel anti-monotone -> hits EtaleThetaQuotient.lean:62-140 (thetaPowerKernel/ellipticPowerKernel normalClosure) + EtTh11ThetaRealizationRowsActual (etTh11_thetaPowerKernel_mono/ellipticPowerKernel_mono anti-monotonicity) -> REUSE (class A: level-factorization maps between mod-l quotients when l1 | l2).

# [EtTh] 13: mod-l quotient factorization along divisibility (class A)

Corpus: papers/motizuki_corpus/text/The Etale Theta Function and its Frobenioid-theoretic
Manifestations.txt, theta-group quotient package.
CLASS A (proved here): if l1 | l2, the mod-l2 theta (resp. elliptic) quotient maps
factor through the mod-l1 maps, via the power-kernel anti-monotonicity of EtTh11.
CLASS B (named): geometric realization / Frobenioid manifestation (unchanged).
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.EtTh13ModLFactorizationActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.EtTh10ThetaQuotientLawsActual
open LeanFormal.IUT.XiFPaper.EtTh11ThetaRealizationRowsActual

universe u

/-- **Level factorization (theta side):** l1 | l2 gives a map of the mod-l2 theta
quotient onto the mod-l1 theta quotient (class A). -/
noncomputable def etTh13_modLThetaFactor (G : Type u) [Group G] {l1 l2 : Nat}
    (h : l1 ∣ l2) :
    ModLThetaQuotient G l2 →* ModLThetaQuotient G l1 :=
  QuotientGroup.map (thetaPowerKernel G l2) (thetaPowerKernel G l1)
    (MonoidHom.id (ThetaQuotient G)) (etTh11_thetaPowerKernel_mono G h)

/-- The factorization composes to the lower-level projection (class A). -/
theorem etTh13_modLThetaFactor_comp (G : Type u) [Group G] {l1 l2 : Nat}
    (h : l1 ∣ l2) :
    (etTh13_modLThetaFactor G h).comp (modLThetaProjection G l2) =
      modLThetaProjection G l1 :=
  rfl

/-- **Level factorization (elliptic side):** l1 | l2 gives a map of the mod-l2
elliptic abelianization onto the mod-l1 one (class A). -/
noncomputable def etTh13_modLEllipticFactor (G : Type u) [Group G] {l1 l2 : Nat}
    (h : l1 ∣ l2) :
    ModLEllipticAbelianization G l2 →* ModLEllipticAbelianization G l1 :=
  QuotientGroup.map (ellipticPowerKernel G l2) (ellipticPowerKernel G l1)
    (MonoidHom.id (EllipticAbelianization G)) (etTh11_ellipticPowerKernel_mono G h)

/-- The elliptic factorization composes to the lower-level elliptic projection. -/
theorem etTh13_modLEllipticFactor_comp (G : Type u) [Group G] {l1 l2 : Nat}
    (h : l1 ∣ l2) :
    (etTh13_modLEllipticFactor G h).comp (modLEllipticProjection G l2) =
      modLEllipticProjection G l1 :=
  rfl

/-- The mod-l factorization rows. -/
def etTh13Rows : List (String × String × String) :=
  [ ("theta mod-l factorization along l1 | l2", "A", "PROVED etTh13_modLThetaFactor / _comp")
  , ("elliptic mod-l factorization along l1 | l2", "A", "PROVED etTh13_modLEllipticFactor / _comp")
  , ("power-kernel anti-monotonicity input", "A", "REUSED EtTh11 etTh11_thetaPowerKernel_mono / etTh11_ellipticPowerKernel_mono")
  , ("geometric realization / Frobenioid manifestation", "B", "NAMED paper inputs; interface only") ]

/-- The mod-l factorization row record has four rows. -/
theorem etTh13Rows_length : etTh13Rows.length = 4 := rfl

#check etTh13_modLThetaFactor
#check etTh13_modLThetaFactor_comp
#check etTh13_modLEllipticFactor
#check etTh13Rows_length

end LeanFormal.IUT.XiFPaper.EtTh13ModLFactorizationActual
end