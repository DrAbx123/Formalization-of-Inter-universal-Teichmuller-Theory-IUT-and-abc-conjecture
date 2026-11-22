/-
  B3 (refined two-chart Cech cover) -- the cover of `Y_n` on which `psi^*O(1)` has a genuine unit.

  ## Why the naive cover does not work

  With `a = psiChart0Coord n T = ∏_{t ∈ T} (x - t)` in the first chart ring `R n`
  and `q = psiChartInfDenom n T` in the infinity chart ring `R2 n`,
  the transition unit of `psi^*O(1)` on the Fermat overlap is
  `psiUnit = r^{|T|} * q⁻¹` (see `Mzk1G1PsiAffineCompatActual`), which is *not*
  a unit of the overlap `Overlap0 n = Localization.Away (x0 n)`: neither `a` nor the
  class of `q` is invertible there.

  ## The refinement

  Inverting `a` fixes this, because on the overlap `r = x⁻¹` and
  `q = a / x^{|T|}`: after inverting `a` both `r` and `q` are units.  Concretely
  (see `beta_algMap_psiChartInfDenom` below),

      beta (algebraMap (R2 n) (OverlapInf n) q) = iu0 ^ |T| * algebraMap (R n) (Overlap0 n) a,

  a product of the unit `iu0` and (the image of) `a`, so it is a unit in
  `A01 = Localization.Away (algebraMap (R n) (Overlap0 n) a)`.

  The refined cover is

  * `A0  = Localization.Away a`        over `R n`   (first chart restricted to `D(a)`),
  * `A1  = Localization.Away q`        over `R2 n`  (infinity chart restricted to `D(q)`),
  * `A01 = Localization.Away (algebraMap (R n) (Overlap0 n) a)` over `Overlap0 n`,

  with `ρ0` the localization lift of `R n → Overlap0 n → A01` and `ρ1` the
  localization lift of `R2 n → OverlapInf n → Overlap0 n → A01` (`beta` in the middle).

  ## Note on the second coordinate

  `b = psiChartInfCoord n T = q⁻¹ r^{|T|}` is *not* claimed to be a unit of `A1`:
  `r` is not inverted in `Away q`.  `b` is merely the regular second-chart
  coordinate of `psi`; the invertibility needed for the transition happens on the overlap
  `A01`, where `r` (hence `q`) is a unit after `a` is inverted.

  No `sorry`; axiom footprint checked at the end of the file.
-/
import tmp.sheaf.xif.paper.AG_FLT_TwoChartCechActual
import tmp.sheaf.xif.paper.Mzk1G1B3CoverActual
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
import tmp.sheaf.xif.paper.Mzk1G1PsiChartMapsActual
import tmp.sheaf.xif.paper.Mzk1G1PsiProductIdentityActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLinePiOverlapActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

noncomputable section

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiProductIdentityActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLinePiOverlapActual

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3RefinedCoverActual

variable (n : Nat) (T : Finset ℚ)

/-! ## The three rings of the refined cover -/

/-- `A0` of the refined cover: the first chart ring `R n` localized at
`a = psiChart0Coord n T`, i.e. the first chart restricted to the principal open
`D(a)`.  (`a` itself is not a unit of `R n`.) -/
noncomputable abbrev refinedChart0 : Type :=
  Localization.Away (psiChart0Coord n T)

/-- `A1` of the refined cover: the infinity chart ring `R2 n` localized at
`q = psiChartInfDenom n T`, i.e. the second chart of `psi` restricted to `D(q)`. -/
noncomputable abbrev refinedChart1 : Type :=
  Localization.Away (psiChartInfDenom n T)

/-- `A01` of the refined cover: the first overlap ring `Overlap0 n` localized at
the image of `a`.  This is the ring on which `a` -- and therefore `r` and `q` --
becomes a unit. -/
noncomputable abbrev refinedOverlap : Type :=
  Localization.Away (algebraMap (R n) (Overlap0 n) (psiChart0Coord n T))

/-! ## `ρ0 : A0 → A01` -/

/-- The `ℚ`-algebra map `R n → A01` underlying `ρ0`: first chart ring,
then the first overlap `Overlap0 n`, then `A01`. -/
noncomputable def chart0RingToRefinedOverlap : R n →ₐ[ℚ] refinedOverlap n T where
  toRingHom :=
    (algebraMap (Overlap0 n) (refinedOverlap n T)).comp (algebraMap (R n) (Overlap0 n))
  commutes' r := by
    have h : ((algebraMap (Overlap0 n) (refinedOverlap n T)).comp
        (algebraMap (R n) (Overlap0 n))).comp (algebraMap ℚ (R n)) =
        algebraMap ℚ (refinedOverlap n T) := RingHom.ext_rat _ _
    exact RingHom.congr_fun h r

/-- `chart0RingToRefinedOverlap` is the composite of the two structure maps. -/
theorem chart0RingToRefinedOverlap_apply (x : R n) :
    chart0RingToRefinedOverlap n T x =
      algebraMap (Overlap0 n) (refinedOverlap n T) (algebraMap (R n) (Overlap0 n) x) :=
  rfl

/-- The first-chart coordinate `a` is a unit of `A01` by construction. -/
theorem a_isUnit_refinedOverlap :
    IsUnit (algebraMap (Overlap0 n) (refinedOverlap n T)
      (algebraMap (R n) (Overlap0 n) (psiChart0Coord n T))) :=
  IsLocalization.Away.algebraMap_isUnit (S := refinedOverlap n T)
    (x := algebraMap (R n) (Overlap0 n) (psiChart0Coord n T))

/-- The image of `a` under `chart0RingToRefinedOverlap` is a unit of `A01`. -/
theorem chart0RingToRefinedOverlap_isUnit :
    IsUnit (chart0RingToRefinedOverlap n T (psiChart0Coord n T)) := by
  rw [chart0RingToRefinedOverlap_apply]
  exact a_isUnit_refinedOverlap n T

/-- `ρ0 : A0 → A01` of the refined cover: the localization lift of
`R n → Overlap0 n → A01` at `a`. -/
noncomputable def refinedRho0 : refinedChart0 n T →ₐ[ℚ] refinedOverlap n T :=
  IsLocalization.Away.liftAlgHom (x := psiChart0Coord n T)
    (f := chart0RingToRefinedOverlap n T) (chart0RingToRefinedOverlap_isUnit n T)

/-! ## `ρ1 : A1 → A01` -/

/-- `beta` as a `ℚ`-algebra homomorphism `OverlapInf n → Overlap0 n`. -/
noncomputable def overlapInfToOverlap0 : OverlapInf n →ₐ[ℚ] Overlap0 n where
  toRingHom := beta n
  commutes' r := beta_rat n r

/-- `overlapInfToOverlap0` is `beta` on underlying elements. -/
theorem overlapInfToOverlap0_apply (x : OverlapInf n) :
    overlapInfToOverlap0 n x = beta n x :=
  rfl

/-- The `ℚ`-algebra map `R2 n → A01` underlying `ρ1`: infinity chart ring,
then `OverlapInf n`, then `beta` to `Overlap0 n`, then `A01`. -/
noncomputable def chartInfRingToRefinedOverlap : R2 n →ₐ[ℚ] refinedOverlap n T where
  toRingHom :=
    (algebraMap (Overlap0 n) (refinedOverlap n T)).comp
      ((beta n).comp (algebraMap (R2 n) (OverlapInf n)))
  commutes' r := by
    have h : ((algebraMap (Overlap0 n) (refinedOverlap n T)).comp
        ((beta n).comp (algebraMap (R2 n) (OverlapInf n)))).comp (algebraMap ℚ (R2 n)) =
        algebraMap ℚ (refinedOverlap n T) := RingHom.ext_rat _ _
    exact RingHom.congr_fun h r

/-- `chartInfRingToRefinedOverlap` is the composite `R2 n → OverlapInf n → Overlap0 n → A01`. -/
theorem chartInfRingToRefinedOverlap_apply (x : R2 n) :
    chartInfRingToRefinedOverlap n T x =
      algebraMap (Overlap0 n) (refinedOverlap n T)
        (beta n (algebraMap (R2 n) (OverlapInf n) x)) :=
  rfl

/-- KEY COMPUTATION: on the overlap, `beta` sends `q = psiChartInfDenom n T` to
`iu0 ^ |T| * a`.  This is the localization-level form of "`r ↦ x⁻¹` and
`q ↦ a / x^{|T|}`". -/
theorem beta_algMap_psiChartInfDenom :
    beta n (algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T)) =
      iu0 n ^ T.card * algebraMap (R n) (Overlap0 n) (psiChart0Coord n T) := by
  have hmain : algebraMap (R n) (Overlap0 n) (psiChart0Coord n T) =
      u0 n ^ T.card *
        beta n (algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T)) := by
    calc algebraMap (R n) (Overlap0 n) (psiChart0Coord n T)
        = beta n (psi n (psiChart0Coord n T)) :=
          (RingHom.congr_fun (beta_comp_psi n) (psiChart0Coord n T)).symm
      _ = beta n (iu1 n ^ T.card *
            algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T)) := by
          rw [psi_psiChart0Coord n T]
      _ = beta n (iu1 n ^ T.card) *
            beta n (algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T)) := by
          rw [map_mul]
      _ = beta n (iu1 n) ^ T.card *
            beta n (algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T)) := by
          rw [map_pow]
      _ = u0 n ^ T.card *
            beta n (algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T)) := by
          rw [beta_iu1]
  have key : iu0 n ^ T.card * algebraMap (R n) (Overlap0 n) (psiChart0Coord n T) =
      beta n (algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T)) := by
    calc iu0 n ^ T.card * algebraMap (R n) (Overlap0 n) (psiChart0Coord n T)
        = iu0 n ^ T.card * (u0 n ^ T.card *
            beta n (algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T))) := by
          rw [hmain]
      _ = (iu0 n ^ T.card * u0 n ^ T.card) *
            beta n (algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T)) := by
          rw [mul_assoc]
      _ = 1 * beta n (algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T)) := by
          rw [← mul_pow, iu0_mul_u0, one_pow]
      _ = beta n (algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T)) := one_mul _
  exact key.symm

/-- The image of `q` in `A01` is a unit: it is `iu0 ^ |T| * a` there, a product
of a unit of `Overlap0 n` and of the inverted first-chart coordinate `a`. -/
theorem chartInfRingToRefinedOverlap_isUnit :
    IsUnit (chartInfRingToRefinedOverlap n T (psiChartInfDenom n T)) := by
  have h : chartInfRingToRefinedOverlap n T (psiChartInfDenom n T) =
      algebraMap (Overlap0 n) (refinedOverlap n T)
        (iu0 n ^ T.card * algebraMap (R n) (Overlap0 n) (psiChart0Coord n T)) := by
    rw [chartInfRingToRefinedOverlap_apply, beta_algMap_psiChartInfDenom]
  rw [h, map_mul, map_pow]
  exact
    IsUnit.mul
      ((IsUnit.map (algebraMap (Overlap0 n) (refinedOverlap n T))
        (iu0_isUnit n)).pow T.card)
      (a_isUnit_refinedOverlap n T)

/-- `ρ1 : A1 → A01` of the refined cover: the localization lift at `q` of the
composite `R2 n → OverlapInf n → Overlap0 n → A01`. -/
noncomputable def refinedRho1 : refinedChart1 n T →ₐ[ℚ] refinedOverlap n T :=
  IsLocalization.Away.liftAlgHom (x := psiChartInfDenom n T)
    (f := chartInfRingToRefinedOverlap n T) (chartInfRingToRefinedOverlap_isUnit n T)

/-! ## The refined cover and `L = psi^*O(1)` -/

/-- The REFINED two-chart Cech cover of `Y_n`: first chart on `D(a)`, infinity
chart on `D(q)`, common overlap `Away (a)` over `Overlap0 n`. -/
noncomputable def fermatRefinedCover : TwoChartCech.Cover ℚ where
  A0 := refinedChart0 n T
  A1 := refinedChart1 n T
  A01 := refinedOverlap n T
  ρ0 := refinedRho0 n T
  ρ1 := refinedRho1 n T

theorem fermatRefinedCover_A0 : (fermatRefinedCover n T).A0 = refinedChart0 n T := rfl

theorem fermatRefinedCover_A1 : (fermatRefinedCover n T).A1 = refinedChart1 n T := rfl

theorem fermatRefinedCover_A01 : (fermatRefinedCover n T).A01 = refinedOverlap n T := rfl

/-- The genuine transition unit of `psi^*O(1)` on the refined overlap `A01`: the
image of `a = psiChart0Coord n T`, inverted by the localization. -/
noncomputable def refinedLunit : (fermatRefinedCover n T).A01ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := refinedOverlap n T)
    (x := algebraMap (R n) (Overlap0 n) (psiChart0Coord n T))).unit

/-- L := psi^* O(1) (route B3, L at projectiveLineGlued; a := psi coordinate, b := infinity
coordinate), realized as the line bundle of the refined two-chart Cech cover of `Y_n`: the
transition function is the unit `refinedLunit = a` on `A01`. -/
noncomputable def psiPullbackO1 : TwoChartCech.Sections (fermatRefinedCover n T) :=
  (fermatRefinedCover n T).lineBundle (refinedLunit n T)

/-! ## Axiom footprint -/

#print axioms chart0RingToRefinedOverlap
#print axioms chart0RingToRefinedOverlap_apply
#print axioms a_isUnit_refinedOverlap
#print axioms chart0RingToRefinedOverlap_isUnit
#print axioms refinedRho0
#print axioms overlapInfToOverlap0
#print axioms overlapInfToOverlap0_apply
#print axioms chartInfRingToRefinedOverlap
#print axioms chartInfRingToRefinedOverlap_apply
#print axioms beta_algMap_psiChartInfDenom
#print axioms chartInfRingToRefinedOverlap_isUnit
#print axioms refinedRho1
#print axioms fermatRefinedCover
#print axioms fermatRefinedCover_A0
#print axioms fermatRefinedCover_A1
#print axioms fermatRefinedCover_A01
#print axioms refinedLunit
#print axioms psiPullbackO1

end LeanFormal.IUT.XiFPaper.Mzk1G1B3RefinedCoverActual
