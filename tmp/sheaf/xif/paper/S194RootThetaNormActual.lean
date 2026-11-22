import tmp.sheaf.xif.paper.S185HaarRootThetaActual

/-! # S194: actual root-theta norm normalization

For the actual q unit in the completion, define the normalized root norm

  rootThetaNorm v = ||qUnit v||^(1/(2l)).

This is the actual numerical norm normalization corresponding to
root theta = q^(1/(2l)).  It satisfies

  (rootThetaNorm v)^(2l) = ||qUnit v||,

and is attached to the actual paperRootThetaUnit family and completion Haar.

No inequality/no fake norm/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S194RootThetaNormActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.S185HaarRootThetaActual
open MeasureTheory

universe u v

variable {l : PrimeGeFive} {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]

/-- Actual normalized root theta norm: ||qUnit||^(1/(2l)). -/
noncomputable def rootThetaNorm
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
    (v : V) : Real :=
  ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ^
    (1 / (2 * l.value : Real))

theorem rootThetaNorm_pos
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
    (v : V) : 0 < rootThetaNorm G v := by
  unfold rootThetaNorm
  exact Real.rpow_pos_of_pos
    (norm_pos_iff.mpr (Units.ne_zero (G.qUnit v))) _

theorem rootThetaNorm_pow_twoL
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
    (v : V) :
    (rootThetaNorm G v) ^ (2 * l.value) =
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ := by
  unfold rootThetaNorm
  have hx : 0 ≤ ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ :=
    norm_nonneg _
  have hl : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.prime.ne_zero
  have hden : (2 * l.value : Real) ≠ 0 := by positivity
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]
  have hcoef : (1 / (2 * l.value : Real)) * (↑(2 * l.value) : Real) = 1 := by
    push_cast
    field_simp
  rw [hcoef, Real.rpow_one]

/-- Actual root-theta norm normalization object. -/
structure RootThetaNormNormalizationObject
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
    (j : SignedLabel l.value) where
  rootUnit : (v : V) → (RootExtension (G := G) v)ˣ
  rootUnit_eq : rootUnit = fun v => paperRootThetaUnit (G := G) j v
  qUnit : (v : V) → CommonPrimeCompletion (G.place v)
  qUnit_eq : qUnit = fun v => (G.qUnit v : CommonPrimeCompletion (G.place v))
  rootNorm : (v : V) → Real
  rootNorm_eq : rootNorm = rootThetaNorm G
  rootNorm_pos : ∀ v, 0 < rootNorm v
  rootNorm_pow_twoL : ∀ v, (rootNorm v) ^ (2 * l.value) = ‖qUnit v‖
  completionHaar : (v : V) → Measure (CommonPrimeCompletion (G.place v))
  completionHaar_eq : completionHaar = fun v => completionAddHaar (G.place v)

/-- Actual root-theta norm normalization object. -/
noncomputable def rootThetaNormNormalizationObject
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
    (j : SignedLabel l.value) :
    RootThetaNormNormalizationObject G j where
  rootUnit := fun v => paperRootThetaUnit (G := G) j v
  rootUnit_eq := rfl
  qUnit := fun v => (G.qUnit v : CommonPrimeCompletion (G.place v))
  qUnit_eq := rfl
  rootNorm := rootThetaNorm G
  rootNorm_eq := rfl
  rootNorm_pos := rootThetaNorm_pos G
  rootNorm_pow_twoL := rootThetaNorm_pow_twoL G
  completionHaar := fun v => completionAddHaar (G.place v)
  completionHaar_eq := rfl

end LeanFormal.IUT.XiFPaper.S194RootThetaNormActual

end
