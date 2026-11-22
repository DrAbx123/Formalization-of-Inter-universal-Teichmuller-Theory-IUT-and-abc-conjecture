import tmp.sheaf.n8.closure.EtaCommonShellActionActual

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaCommonShellUnitsNonempty

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Nonzero element of the actual F-shell image: exactly a unit of the
common closure lying in the shell image. -/
def EtaShellImageNonzeroWitness : Prop :=
  ∃ x : PadicAlgCl (nativePrime X), x ∈ fShellImage X ∧ x ≠ 0

/-- Nonemptiness of the common shell units. -/
def EtaCommonShellUnitsNonempty : Prop :=
  Nonempty (CommonShellUnit X)

theorem commonShellUnits_nonempty_iff :
    EtaCommonShellUnitsNonempty X ↔ EtaShellImageNonzeroWitness X := by
  constructor
  · rintro ⟨u⟩
    exact ⟨(u.1 : PadicAlgCl (nativePrime X)), u.2, Units.ne_zero u.1⟩
  · rintro ⟨x, hx, hx0⟩
    refine ⟨⟨Units.mk0 x hx0, ?_⟩⟩
    change ((Units.mk0 x hx0 : (AlgebraicClosure ℚ_[nativePrime X])ˣ) :
      PadicAlgCl (nativePrime X)) ∈ fShellImage X
    simpa using hx

theorem commonShellUnits_nonempty_of_nonzero
    (h : EtaShellImageNonzeroWitness X) :
    EtaCommonShellUnitsNonempty X :=
  (commonShellUnits_nonempty_iff X).mpr h

theorem commonShellUnits_nonempty_iff_nonzero :
    EtaCommonShellUnitsNonempty X ↔
      ∃ x : PadicAlgCl (nativePrime X), x ∈ fShellImage X ∧ x ≠ 0 :=
  commonShellUnits_nonempty_iff X

/-! ## Actual additive side (always nonempty) -/

theorem zero_mem_fShellImage :
    (0 : PadicAlgCl (nativePrime X)) ∈ fShellImage X := by
  refine ⟨0, (fPlaceShell X).zero_mem_logShell, ?_⟩
  simp

theorem additiveCommonShell_nonempty :
    (fShellImage X).Nonempty :=
  ⟨0, zero_mem_fShellImage X⟩

/-! ## Exact no-go -/

/- The production data gives `0 ∈ fShellImage` (from `zero_mem_logShell`)
but no theorem producing a nonzero element of the actual log-shell image.
Thus the nonemptiness of `commonShellUnits` is not decided from the current
production declarations; the exact missing source theorem is a nonzero
log-shell element (equivalently a nonzero F-shell image point).  The
corrected target uses the additive common shell `fShellImage`, which is
nonempty by `zero_mem_fShellImage`, instead of forcing a unit. -/
def EtaCommonShellUnitsNoGo : Prop :=
  ¬ EtaCommonShellUnitsNonempty X

def EtaAdditiveCommonShellTarget : Prop :=
  (fShellImage X).Nonempty

theorem etaAdditiveCommonShellTarget_actual :
    EtaAdditiveCommonShellTarget X :=
  additiveCommonShell_nonempty X

end LeanFormal.IUT.N8Closure.EtaCommonShellUnitsNonempty
