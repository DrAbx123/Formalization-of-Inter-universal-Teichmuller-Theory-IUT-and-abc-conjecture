import tmp.sheaf.xif.paper.Mzk1G1B3RefinedCoverActual
import tmp.sheaf.xif.paper.Mzk1TwoChartCechLineBundleIsoActual
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

/-
  B3 (Y-level, first identity) -- phi^*O(1) ~= L^{⊗ d} on Y_n at the Cech level.

  ## What this file proves

  With L = psi^*O(1) realized on a refined two-chart Cech cover of Y_n (route B3,
  S7 Mzk1G1B3RefinedCoverActual.psiPullbackO1), with phi = psi >>> h for a polynomial
  h : Q[lambda] and d = h.natDegree, the two pullbacks of O(1) agree on Y_n:

      phi^*O(1) = psi^*(h^*O(1)) ~= psi^*(O(d)) = (psi^*O(1))^{⊗ d} = L^{⊗ d}.

  This is the FIRST identity of the h-part of the route B3 refinement.  The P1
  ingredient h^*O(1) = O(natDegree h) is proved on the projective-line cover in
  Mzk1G1B3HPullbackActual.b3_h_pullbackO1_iso (22:47:08).  That statement is *not*
  consumed here: it lives on a different cover, and the Y_n-level statement below is a
  purely multiplicative unit computation on a single refined cover of Y_n (see
  transition_relation).  Together the two statements identify the h-pullback of O(1)
  with the d-th tensor power of L on Y_n.

  ## The refined cover of Y_n used here

  Let a = psiChart0Coord n T in R n (the product over t in T of x - t, the first
  coordinate of psi) and let hA = aeval a h in R n be the first coordinate of
  phi = psi >>> h.  Write u = a * hA for their product.  The cover is

  * A0  = Localization.Away u                                  over R n,
  * A1  = refinedChart1 n T = Localization.Away q             over R2 n (q = psiChartInfDenom n T),
  * A01 = Localization.Away (algebraMap (R n) (Overlap0 n) u) over Overlap0 n,

  i.e. the S7 cover (refinedChart0 = Away a, refinedOverlap = Away (a-image)) refined
  once more so that hA becomes a unit too.  Inverting the single element u inverts both
  factors: a and hA are units of A0 and their images are units of A01 (via
  IsLocalization.Away.isUnit_of_dvd applied to the divisibility a | u and hA | u).
  Equivalently, A0 is R n first localized at a (the S7 ring refinedChart0 n T) and then
  at the image of hA, and A01 is the S7 refined overlap further localized at the image of
  hA; this file realizes that iterated localization as the single localization at the
  product u (a Localization.Away nested inside a Localization.Away does not elaborate
  through IsLocalization.Away.liftAlgHom, so only single localization layers are used,
  exactly as in S7).

  The transition units are

  * psiPullbackO1PowUnitH = (unit of a)^{d}, the transition unit of L^{⊗ d}
    (L has transition unit the image of a, cf. S7 refinedLunit),
  * phiPullbackO1UnitH = the unit of the image of hA, the transition unit of
    phi^*O(1) = psi^*(h^*O(1)).

  On the overlap A01 the two differ by the Cech coboundary
  a0 = (unit of hA) * (unit of a ^ d)^{-1} in A0^x and a1 = 1 in A1^x:

      phiUnit * rho1 1 = rho0 a0 * psiPowUnit        (transition_relation),

  which is the value identity hA = hA in A01 (the inverse of a^d cancels against the
  d-th power of the a-unit).  The coboundary criterion
  TwoChartCech.Cover.lineBundle_iso_of_unit_val of Mzk1TwoChartCechLineBundleIsoActual
  then yields phi^*O(1) ~= L^{⊗ d} on Y_n.

  No sorry; the axiom footprint is checked at the end of the file.
-/

noncomputable section

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

open LeanFormal.IUT.XiFPaper.Mzk1G1B3RefinedCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3PullbackO1YActual

variable (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)

/-! ## hA = h(a) and the three rings of the h-refined cover of Y_n -/

/-- The first coordinate of phi = psi >>> h: h evaluated at the first coordinate
a = psiChart0Coord n T of psi.  This is the element hA of R n which the S7 cover of Y_n
does not invert. -/
noncomputable abbrev psiHA : R n := (Polynomial.aeval (psiChart0Coord n T)) h

/-- The product u = a * hA, the element at which the h-refined cover localizes.  Since u
is inverted, both a and hA are units. -/
noncomputable abbrev psiProd : R n := psiChart0Coord n T * psiHA n T h

/-- A0 of the h-refined cover: R n localized at u = a * hA.  Both a and hA are units of
A0. -/
noncomputable abbrev hChart0 : Type :=
  Localization.Away (psiProd n T h)

/-- A01 of the h-refined cover: the S7 overlap ring Overlap0 n localized at the image of
u = a * hA.  On it, both a and hA are units. -/
noncomputable abbrev hOverlap : Type :=
  Localization.Away (algebraMap (R n) (Overlap0 n) (psiProd n T h))

/-- The structure ring hom Overlap0 n -> A01. -/
noncomputable def hOverlapRing : Overlap0 n →+* hOverlap n T h :=
  algebraMap (Overlap0 n) (hOverlap n T h)

/-- The structure monoid hom Overlap0 n -> A01. -/
noncomputable def hOverlapMonoidHom : Overlap0 n →* hOverlap n T h :=
  (hOverlapRing n T h).toMonoidHom

/-! ## R n -> A01 and rho0 : A0 -> A01 -/

/-- The Q-algebra map R n -> A01 underlying rho0: first chart ring R n, then the S7 first
overlap Overlap0 n, then A01. -/
noncomputable def chart0ToA01 : R n →ₐ[ℚ] hOverlap n T h where
  toRingHom := (hOverlapRing n T h).comp (algebraMap (R n) (Overlap0 n))
  commutes' r := by
    have hc : ((hOverlapRing n T h).comp (algebraMap (R n) (Overlap0 n))).comp
        (algebraMap ℚ (R n)) = algebraMap ℚ (hOverlap n T h) := RingHom.ext_rat _ _
    exact RingHom.congr_fun hc r

/-- chart0ToA01 is the composite of the two structure maps. -/
theorem chart0ToA01_apply (x : R n) :
    chart0ToA01 n T h x = hOverlapRing n T h (algebraMap (R n) (Overlap0 n) x) :=
  rfl

/-- The image in A01 of u = a * hA is a unit: A01 is the localization at that element. -/
theorem chart0ToA01_prod_isUnit : IsUnit (chart0ToA01 n T h (psiProd n T h)) := by
  rw [chart0ToA01_apply]
  exact IsLocalization.Away.algebraMap_isUnit (S := hOverlap n T h)
    (x := algebraMap (R n) (Overlap0 n) (psiProd n T h))

/-- The image of a in A01 is a unit: a divides the inverted product u. -/
theorem aImg_isUnit :
    IsUnit (hOverlapRing n T h (algebraMap (R n) (Overlap0 n) (psiChart0Coord n T))) :=
  IsLocalization.Away.isUnit_of_dvd
    (x := algebraMap (R n) (Overlap0 n) (psiProd n T h))
    (r := algebraMap (R n) (Overlap0 n) (psiChart0Coord n T))
    ⟨algebraMap (R n) (Overlap0 n) (psiHA n T h), by rw [← map_mul]⟩

/-- The image of hA in A01 is a unit: hA divides the inverted product u. -/
theorem hAImg_isUnit :
    IsUnit (hOverlapRing n T h (algebraMap (R n) (Overlap0 n) (psiHA n T h))) :=
  IsLocalization.Away.isUnit_of_dvd
    (x := algebraMap (R n) (Overlap0 n) (psiProd n T h))
    (r := algebraMap (R n) (Overlap0 n) (psiHA n T h))
    ⟨algebraMap (R n) (Overlap0 n) (psiChart0Coord n T), by rw [mul_comm, ← map_mul]⟩

/-- rho0 : A0 -> A01 of the h-refined cover: the localization lift at u of
R n -> Overlap0 n -> A01. -/
noncomputable def rho0H : hChart0 n T h →ₐ[ℚ] hOverlap n T h :=
  IsLocalization.Away.liftAlgHom (x := psiProd n T h) (f := chart0ToA01 n T h)
    (chart0ToA01_prod_isUnit n T h)

/-- rho0 sends the image of x : R n to chart0ToA01 x. -/
theorem rho0H_algebraMap (x : R n) :
    rho0H n T h (algebraMap (R n) (hChart0 n T h) x) = chart0ToA01 n T h x := by
  simp [rho0H]

/-! ## rho1 : A1 -> A01 -/

/-- The Q-algebra map R2 n -> A01 underlying rho1: infinity chart ring R2 n, then
OverlapInf n, then beta to Overlap0 n, then A01. -/
noncomputable def chartInfToA01 : R2 n →ₐ[ℚ] hOverlap n T h where
  toRingHom :=
    (hOverlapRing n T h).comp ((beta n).comp (algebraMap (R2 n) (OverlapInf n)))
  commutes' r := by
    have hc : ((hOverlapRing n T h).comp
        ((beta n).comp (algebraMap (R2 n) (OverlapInf n)))).comp (algebraMap ℚ (R2 n)) =
        algebraMap ℚ (hOverlap n T h) := RingHom.ext_rat _ _
    exact RingHom.congr_fun hc r

/-- chartInfToA01 is the composite R2 n -> OverlapInf n -> Overlap0 n -> A01. -/
theorem chartInfToA01_apply (x : R2 n) :
    chartInfToA01 n T h x =
      hOverlapRing n T h (beta n (algebraMap (R2 n) (OverlapInf n) x)) :=
  rfl

/-- Value of chartInfToA01 at q = psiChartInfDenom n T: beta sends q to
iu0 ^ |T| * a, so the value is the product of the iu0-image and the a-image. -/
theorem chartInfToA01_q_val :
    chartInfToA01 n T h (psiChartInfDenom n T) =
      hOverlapRing n T h (iu0 n) ^ T.card *
        hOverlapRing n T h (algebraMap (R n) (Overlap0 n) (psiChart0Coord n T)) := by
  calc chartInfToA01 n T h (psiChartInfDenom n T)
      = hOverlapRing n T h
          (beta n (algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T))) :=
        chartInfToA01_apply n T h _
    _ = hOverlapRing n T h
          (iu0 n ^ T.card * algebraMap (R n) (Overlap0 n) (psiChart0Coord n T)) := by
        rw [beta_algMap_psiChartInfDenom]
    _ = hOverlapRing n T h (iu0 n ^ T.card) *
          hOverlapRing n T h (algebraMap (R n) (Overlap0 n) (psiChart0Coord n T)) :=
        map_mul _ _ _
    _ = hOverlapRing n T h (iu0 n) ^ T.card *
          hOverlapRing n T h (algebraMap (R n) (Overlap0 n) (psiChart0Coord n T)) := by
        rw [map_pow]

/-- The image of q = psiChartInfDenom n T in A01 is a unit: it is a product of the
iu0-image and the a-image, both units of A01. -/
theorem chartInfToA01_q_isUnit : IsUnit (chartInfToA01 n T h (psiChartInfDenom n T)) := by
  have hprod : IsUnit (hOverlapRing n T h (iu0 n) ^ T.card *
      hOverlapRing n T h (algebraMap (R n) (Overlap0 n) (psiChart0Coord n T))) :=
    IsUnit.mul ((IsUnit.map (hOverlapMonoidHom n T h) (iu0_isUnit n)).pow T.card)
      (aImg_isUnit n T h)
  obtain ⟨u, hu⟩ := hprod
  exact ⟨u, hu.trans (chartInfToA01_q_val n T h).symm⟩

/-- rho1 : A1 -> A01 of the h-refined cover: the localization lift at q of
R2 n -> OverlapInf n -> Overlap0 n -> A01. -/
noncomputable def rho1H : refinedChart1 n T →ₐ[ℚ] hOverlap n T h :=
  IsLocalization.Away.liftAlgHom (x := psiChartInfDenom n T) (f := chartInfToA01 n T h)
    (chartInfToA01_q_isUnit n T h)

/-! ## The h-refined cover of Y_n -/

/-- The h-refined two-chart Cech cover of Y_n: first chart D(u) = D(a) ∩ D(h(a)),
infinity chart D(q) (the S7 refinedChart1), and the S7 first overlap localized at the
image of u. -/
noncomputable def fermatRefinedCoverH : TwoChartCech.Cover ℚ where
  A0 := hChart0 n T h
  A1 := refinedChart1 n T
  A01 := hOverlap n T h
  ρ0 := rho0H n T h
  ρ1 := rho1H n T h

theorem fermatRefinedCoverH_A0 : (fermatRefinedCoverH n T h).A0 = hChart0 n T h := rfl

theorem fermatRefinedCoverH_A1 : (fermatRefinedCoverH n T h).A1 = refinedChart1 n T := rfl

theorem fermatRefinedCoverH_A01 : (fermatRefinedCoverH n T h).A01 = hOverlap n T h := rfl

/-! ## The two transition units -/

/-- The unit of a = psiChart0Coord n T in A01. -/
noncomputable def aUnitA01H : (hOverlap n T h)ˣ := (aImg_isUnit n T h).unit

/-- Value of aUnitA01H. -/
theorem aUnitA01H_val :
    (aUnitA01H n T h : hOverlap n T h) =
      hOverlapRing n T h (algebraMap (R n) (Overlap0 n) (psiChart0Coord n T)) :=
  IsUnit.unit_spec _

/-- The transition unit of phi^*O(1) on the h-refined overlap: the unit of the image of
hA = h(a) in A01. -/
noncomputable def phiPullbackO1UnitH : (hOverlap n T h)ˣ :=
  (hAImg_isUnit n T h).unit

/-- Value of phiPullbackO1UnitH: the image of hA in A01. -/
theorem phiPullbackO1UnitH_val :
    (phiPullbackO1UnitH n T h : hOverlap n T h) =
      hOverlapRing n T h (algebraMap (R n) (Overlap0 n) (psiHA n T h)) :=
  IsUnit.unit_spec _

/-- The transition unit of L^{⊗ d}: the d-th power of the a-unit, d = h.natDegree. -/
noncomputable def psiPullbackO1PowUnitH : (hOverlap n T h)ˣ :=
  aUnitA01H n T h ^ h.natDegree

/-- Value of psiPullbackO1PowUnitH: the d-th power of the image of a in A01. -/
theorem psiPullbackO1PowUnitH_val :
    (psiPullbackO1PowUnitH n T h : hOverlap n T h) =
      (aUnitA01H n T h : hOverlap n T h) ^ h.natDegree :=
  Units.val_pow_eq_pow_val (aUnitA01H n T h) h.natDegree

/-! ## The A0-units and the coboundary a0 -/

/-- The image of a in A0 is a unit: a divides the inverted product u. -/
theorem aImgA0_isUnit : IsUnit (algebraMap (R n) (hChart0 n T h) (psiChart0Coord n T)) :=
  IsLocalization.Away.isUnit_of_dvd (x := psiProd n T h) (r := psiChart0Coord n T)
    ⟨psiHA n T h, rfl⟩

/-- The image of hA in A0 is a unit: hA divides the inverted product u. -/
theorem hAImgA0_isUnit : IsUnit (algebraMap (R n) (hChart0 n T h) (psiHA n T h)) :=
  IsLocalization.Away.isUnit_of_dvd (x := psiProd n T h) (r := psiHA n T h)
    ⟨psiChart0Coord n T, by rw [mul_comm]⟩

/-- The unit of a in A0. -/
noncomputable def aUnitA0 : (hChart0 n T h)ˣ := (aImgA0_isUnit n T h).unit

/-- Value of aUnitA0. -/
theorem aUnitA0_val :
    (aUnitA0 n T h : hChart0 n T h) =
      algebraMap (R n) (hChart0 n T h) (psiChart0Coord n T) :=
  IsUnit.unit_spec _

/-- The unit hA = h(a) of A0, i.e. the first component of the Cech coboundary
trivializing phi^*O(1). -/
noncomputable def hAUnitA0 : (hChart0 n T h)ˣ := (hAImgA0_isUnit n T h).unit

/-- Value of hAUnitA0. -/
theorem hAUnitA0_val :
    (hAUnitA0 n T h : hChart0 n T h) =
      algebraMap (R n) (hChart0 n T h) (psiHA n T h) :=
  IsUnit.unit_spec _

/-- The Cech coboundary relating the two transition units: hA * (a^d)^{-1} in A0^x
(both hA and a are units of A0), d = h.natDegree. -/
noncomputable def a0H : (hChart0 n T h)ˣ :=
  hAUnitA0 n T h * (aUnitA0 n T h ^ h.natDegree)⁻¹

/-! ## The coboundary relation -/

/-- Value of rho0 (hAUnitA0) in A01: the image of hA, i.e. the transition unit of
phi^*O(1). -/
theorem rho0H_hAUnitA0_val :
    rho0H n T h (hAUnitA0 n T h : hChart0 n T h) =
      (phiPullbackO1UnitH n T h : hOverlap n T h) := by
  rw [hAUnitA0_val, rho0H_algebraMap, chart0ToA01_apply]
  exact (phiPullbackO1UnitH_val n T h).symm

/-- Value of rho0 (aUnitA0) in A01: the image of a, i.e. the transition unit of L. -/
theorem rho0H_aUnitA0_val :
    rho0H n T h (aUnitA0 n T h : hChart0 n T h) =
      (aUnitA01H n T h : hOverlap n T h) := by
  rw [aUnitA0_val, rho0H_algebraMap, chart0ToA01_apply]
  exact (aUnitA01H_val n T h).symm

/-- Value of rho0 (a0) in A01: the hA-unit times the inverse of the d-th power of the
a-image. -/
theorem rho0H_a0H_val :
    rho0H n T h (a0H n T h : hChart0 n T h) =
      (phiPullbackO1UnitH n T h : hOverlap n T h) *
        rho0H n T h (↑((aUnitA0 n T h ^ h.natDegree)⁻¹) : hChart0 n T h) := by
  rw [a0H, Units.val_mul, map_mul, rho0H_hAUnitA0_val]

/-- The inverse of the d-th power of the a-unit maps to an inverse of the d-th power of
its image in A01: both statements live on the overlap A01, where rho0 is multiplicative. -/
theorem psiPowUnit_inv_mul :
    rho0H n T h (↑((aUnitA0 n T h ^ h.natDegree)⁻¹) : hChart0 n T h) *
        (aUnitA01H n T h : hOverlap n T h) ^ h.natDegree = 1 := by
  have hmul : (↑((aUnitA0 n T h ^ h.natDegree)⁻¹) : hChart0 n T h) *
      (↑(aUnitA0 n T h ^ h.natDegree) : hChart0 n T h) = 1 :=
    Units.inv_mul _
  have hmap := congrArg (⇑(rho0H n T h)) hmul
  rw [map_mul, map_one, Units.val_pow_eq_pow_val, map_pow, rho0H_aUnitA0_val] at hmap
  exact hmap

/-- KEY COMPUTATION.  On the h-refined cover of Y_n the transition units of phi^*O(1)
and of L^{⊗ d} differ by the Cech coboundary (a0, 1): since both a and hA are units of
A0, the relation reduces to hA = hA * (a^d)^{-1} * a^d in A01. -/
theorem transition_relation :
    (phiPullbackO1UnitH n T h : hOverlap n T h) * rho1H n T h (1 : refinedChart1 n T) =
      rho0H n T h (a0H n T h : hChart0 n T h) *
        (psiPullbackO1PowUnitH n T h : hOverlap n T h) := by
  rw [map_one, mul_one, rho0H_a0H_val, psiPullbackO1PowUnitH_val, mul_assoc,
    psiPowUnit_inv_mul, mul_one]

/-! ## phi^*O(1) ~= L^{⊗ d} -/

/-- B3 (Y-level, first identity).  For a nonzero polynomial h : Q[lambda] and
d = h.natDegree, the pullback phi^*O(1) of O(1) along phi = psi >>> h, realized on the
h-refined cover of Y_n with transition unit phiPullbackO1UnitH (the image of h(a)), is
isomorphic to the d-th tensor power L^{⊗ d} of L = psi^*O(1), realized on the same cover
with transition unit psiPullbackO1PowUnitH = (unit of a)^d. -/
theorem b3_pullbackO1_iso (hh : h ≠ 0) :
    Nonempty (TwoChartCech.SectionsIso
      ((fermatRefinedCoverH n T h).lineBundle (psiPullbackO1PowUnitH n T h))
      ((fermatRefinedCoverH n T h).lineBundle (phiPullbackO1UnitH n T h))) :=
  TwoChartCech.Cover.lineBundle_iso_of_unit_val (fermatRefinedCoverH n T h)
    (psiPullbackO1PowUnitH n T h) (phiPullbackO1UnitH n T h)
    (a0H n T h) (1 : (fermatRefinedCoverH n T h).A1ˣ) (transition_relation n T h)

/-! ## Axiom footprint -/

#print axioms psiHA
#print axioms psiProd
#print axioms hChart0
#print axioms hOverlap
#print axioms hOverlapRing
#print axioms hOverlapMonoidHom
#print axioms chart0ToA01
#print axioms chart0ToA01_apply
#print axioms chart0ToA01_prod_isUnit
#print axioms aImg_isUnit
#print axioms hAImg_isUnit
#print axioms rho0H
#print axioms rho0H_algebraMap
#print axioms chartInfToA01
#print axioms chartInfToA01_apply
#print axioms chartInfToA01_q_val
#print axioms chartInfToA01_q_isUnit
#print axioms rho1H
#print axioms fermatRefinedCoverH
#print axioms fermatRefinedCoverH_A0
#print axioms fermatRefinedCoverH_A1
#print axioms fermatRefinedCoverH_A01
#print axioms aUnitA01H
#print axioms aUnitA01H_val
#print axioms phiPullbackO1UnitH
#print axioms phiPullbackO1UnitH_val
#print axioms psiPullbackO1PowUnitH
#print axioms psiPullbackO1PowUnitH_val
#print axioms aImgA0_isUnit
#print axioms hAImgA0_isUnit
#print axioms aUnitA0
#print axioms aUnitA0_val
#print axioms hAUnitA0
#print axioms hAUnitA0_val
#print axioms a0H
#print axioms rho0H_hAUnitA0_val
#print axioms rho0H_aUnitA0_val
#print axioms rho0H_a0H_val
#print axioms psiPowUnit_inv_mul
#print axioms transition_relation
#print axioms b3_pullbackO1_iso

end LeanFormal.IUT.XiFPaper.Mzk1G1B3PullbackO1YActual