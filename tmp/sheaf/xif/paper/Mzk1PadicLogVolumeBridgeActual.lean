import tmp.sheaf.takkun.IutLean.Padic.LogVolume
import tmp.sheaf.takkun.IutLean.Padic.LogShellRadius
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual

/-! # Mzk1PadicLogVolumeBridgeActual — A502 object-level normalization lemma list

Object-construction (no wiring): packages the Takkun p-adic log-volume normalization laws
(`logVol`, `logVol_pow`, `logShellVolFormula`) as a definition-level object, and lists the
own-side C3 tensor normalization law (`c3TensorBlockDimension` p-scaling) next to it, so the
hull construction can consume both layers.  The tensor-dimension bridge itself is left as a
documented target (needs the coordinate construction), not asserted.  No sorry/axiom.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PadicLogVolumeBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory

/-- Object: the Takkun p-adic log-volume normalization (μ_log) with its proved laws. -/
structure PadicLogVolumeNormalization (p : ℕ) [Fact p.Prime] : Type where
  vol : ℚ_[p] → ℝ
  vol_one : vol 1 = 0
  vol_p : vol (p : ℚ_[p]) = -Real.log p
  vol_mul : ∀ {x y : ℚ_[p]}, x ≠ 0 → y ≠ 0 → vol (x * y) = vol x + vol y
  vol_pow : ∀ (x : ℚ_[p]) (n : ℕ), vol (x ^ n) = n * vol x
  vol_logOnePlus : p ≠ 2 → ∀ {x : ℚ_[p]}, ‖x‖ ≤ (p : ℝ)⁻¹ →
    vol (IUT.Padic.logOnePlus x) = vol x
  shell_boundary : p ≠ 2 → ∀ {x : ℚ_[p]}, ‖x‖ = (p : ℝ)⁻¹ →
    vol (IUT.Padic.logOnePlus x) = -(IUT.Padic.aRadius p 1) * Real.log p

/-- **Constructed** from the Takkun proved lemmas (definition-level object, not assumed). -/
def padicLogVolumeNormalization (p : ℕ) [hp : Fact p.Prime] :
    PadicLogVolumeNormalization p where
  vol := IUT.Padic.logVol
  vol_one := IUT.Padic.logVol_one
  vol_p := IUT.Padic.logVol_p
  vol_mul := fun hx hy => IUT.Padic.logVol_mul hx hy
  vol_pow := fun x n => IUT.Padic.logVol_pow x n
  vol_logOnePlus := fun hp2 x hx => IUT.Padic.logVol_logOnePlus hp2 hx
  shell_boundary := fun hp2 x hx => IUT.Padic.logShell_vol_boundary hp2 hx

/-- A502 constructed-object convention. -/
theorem padicLogVolumeNormalization_constructed (p : ℕ) [Fact p.Prime] :
    PadicLogVolumeNormalization p :=
  padicLogVolumeNormalization p

/-! ## Lemma list: Takkun local normalization (re-exported under our namespace) -/

/-- Takkun μ_log normalization: μ_log(p) = -log p. -/
theorem padic_logVol_p (p : ℕ) [Fact p.Prime] :
    IUT.Padic.logVol (p : ℚ_[p]) = -Real.log p := IUT.Padic.logVol_p

/-- Takkun power law: μ_log(x^n) = n μ_log(x) (theta values q^{j²}). -/
theorem padic_logVol_pow (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (n : ℕ) :
    IUT.Padic.logVol (x ^ n) = n * IUT.Padic.logVol x := IUT.Padic.logVol_pow x n

/-- Takkun unramified shell-volume formula: equals -log p. -/
theorem padic_logShellVolFormula_unramified (p : ℕ) [Fact p.Prime] :
    IUT.Padic.logShellVolFormula p 1 1 0 = -Real.log p := IUT.Padic.logShellVolFormula_unramified

/-- Takkun tame radii: for p>2, e≤p-2, a=1/e and b=-1/e (IUT-IV Prop 1.2). -/
theorem padic_radius_tame {p e : ℕ} (hp : 2 < p) (he : 1 ≤ e) (h : e + 2 ≤ p) :
    IUT.Padic.aRadius p e = 1 / (e : ℝ) ∧ IUT.Padic.bRadius p e = -(1 / (e : ℝ)) :=
  IUT.Padic.radius_tame hp he h

/-! ## Own-side counterpart: C3 tensor block normalization (existing PROVED law) -/

/-- Own tensor law: log Haar scales by -(blockDim)*log p under p_v-scaling
(from S3137ThetaHullVolumeScalingActual, same normalization as the Takkun local factor). -/
theorem c3Tensor_logVolume_prime_smul
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal =
      -(c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ) +
        thetaPilotHullLogVolumeReal C3 :=
  thetaPilotHull_log_measure_prime_smul (C3 := C3) hpos

#check PadicLogVolumeNormalization
#check padicLogVolumeNormalization_constructed
#check c3Tensor_logVolume_prime_smul

end LeanFormal.IUT.XiFPaper.Mzk1PadicLogVolumeBridgeActual
end
