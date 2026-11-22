/- B3 second identity: the omega_Y(E_phi) Cech units over the CONCRETE overlap ring.

  Design (approved): avoid the def-wrapped S9 overlap ring; work over Overlap0 n and localise
  once at u := a * hA * f0 where a := psiChart0Coord, hA := phiCoord0 (= h(a)), f0 := ePhiTwistEq0
  = hA*(hA-1) (chart-0 equation of the 0/1 fibres of phi). Every factor is a unit of the
  localization (isUnit_of_dvd from product divisibility), and the A5 omega_Y unit (a unit of
  Overlap0) maps in directly.

  Remaining main theorem: omegaEIsoUnit_eq (pointwise dt/du order identity of route L334).
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1B3PullbackO1YActual
import tmp.sheaf.xif.paper.Mzk1G1B3OmegaETwistActual
import tmp.sheaf.xif.paper.Mzk1G1A5LineBundleIsoActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3OmegaEIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B3OmegaETwistActual

/-- 具体 overlap 环上的单层局部化元素：`a * hA * f0`。 -/
noncomputable def omegaEElem (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) : Overlap0 n :=
  algebraMap (R n) (Overlap0 n)
    (psiChart0Coord n T * phiCoord0 n T h * ePhiTwistEq0 n T h)

/-- 具体 overlap 环 `Overlap0 n` 在 `omegaEElem` 处的局部化（E_φ 的 Cech 单元环）。 -/
abbrev omegaEOverlap (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) : Type :=
  Localization.Away (omegaEElem n T h)

/-- E_φ 的 chart-0 twist 单元：`f0` 的像（f0 整除 omegaEElem）。 -/
noncomputable def twistUnit (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) :
    (omegaEOverlap n T h)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := omegaEOverlap n T h)
    (x := omegaEElem n T h)
    (r := algebraMap (R n) (Overlap0 n) (ePhiTwistEq0 n T h)) (by
      unfold omegaEElem
      have hd0 : ePhiTwistEq0 n T h ∣
          psiChart0Coord n T * phiCoord0 n T h * ePhiTwistEq0 n T h := by
        refine ⟨psiChart0Coord n T * phiCoord0 n T h, ?_⟩
        ring
      exact map_dvd _ hd0)).unit

/-- ω_Y 的单元推入 `omegaEOverlap`（A5 `omegaYEUnit` 是 Overlap0 的单位）。 -/
noncomputable def omegaUnitExt (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) :
    (omegaEOverlap n T h)ˣ :=
  Units.map (algebraMap (Overlap0 n) (omegaEOverlap n T h)).toMonoidHom (omegaYEUnit n)

/-- φ^*O(1) 的单元推入 `omegaEOverlap`（`hA` 的像，hA 整除 omegaEElem）。 -/
noncomputable def phiUnitExt (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) :
    (omegaEOverlap n T h)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := omegaEOverlap n T h)
    (x := omegaEElem n T h)
    (r := algebraMap (R n) (Overlap0 n) (phiCoord0 n T h)) (by
      unfold omegaEElem
      have hd0 : phiCoord0 n T h ∣
          psiChart0Coord n T * phiCoord0 n T h * ePhiTwistEq0 n T h := by
        refine ⟨psiChart0Coord n T * ePhiTwistEq0 n T h, ?_⟩
        ring
      exact map_dvd _ hd0)).unit

/-- **ω_Y(E_φ) 的过渡单元** = ω_Y 单元 ⊗ E_φ twist 单元。 -/
noncomputable def omegaEIsoUnit (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) :
    (omegaEOverlap n T h)ˣ :=
  omegaUnitExt n T h * twistUnit n T h

theorem omegaEIsoUnit_def (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) :
    omegaEIsoUnit n T h = omegaUnitExt n T h * twistUnit n T h := rfl

theorem twistUnit_val (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) :
    (twistUnit n T h : omegaEOverlap n T h) =
      algebraMap (Overlap0 n) (omegaEOverlap n T h)
        (algebraMap (R n) (Overlap0 n) (ePhiTwistEq0 n T h)) :=
  IsUnit.unit_spec _

theorem phiUnitExt_val (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) :
    (phiUnitExt n T h : omegaEOverlap n T h) =
      algebraMap (Overlap0 n) (omegaEOverlap n T h)
        (algebraMap (R n) (Overlap0 n) (phiCoord0 n T h)) :=
  IsUnit.unit_spec _

#print axioms omegaEElem
#print axioms twistUnit
#print axioms omegaUnitExt
#print axioms phiUnitExt
#print axioms omegaEIsoUnit
#print axioms twistUnit_val
#print axioms phiUnitExt_val

end LeanFormal.IUT.XiFPaper.Mzk1G1B3OmegaEIsoActual