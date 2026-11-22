import tmp.sheaf.xif.paper.S194RootThetaNormActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual

/-! # S201: rootThetaNorm vs the actual L norm of rootNormedThetaValueInL

This file proves the actual norm relation for the L-model of the root theta
value:

  ||rootNormedElement||^(2l) = ||sourceRootQUnit||,
  ||rootNormedThetaValueInL j|| = ||rootNormedElement||^(j^2),

and the exact comparison with S194 rootThetaNorm for a completion geometry whose
qUnit norm matches sourceRootQUnit.

No inequality/no fake norm/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.S194RootThetaNormActual

universe u v

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]

/-- Actual L root norm: norm of the rootNormedElement. -/
noncomputable def rootNormedElementNorm : Real :=
  ‖rootNormedElement T b‖

/-- The actual L root norm has the defining 2l-th norm power. -/
theorem rootNormedElementNorm_pow_twoL :
    (rootNormedElementNorm T b) ^ (2 * l.value) =
      ‖(sourceRootQUnit T b : rootBase T b)‖ := by
  unfold rootNormedElementNorm
  have h := congrArg (fun x : rootNormedAmbient T b => ‖x‖)
    (rootNormedElement_pow T b)
  rw [norm_pow] at h
  rw [h]
  simpa [unitToAlgClosed, norm_algebraMap']

/-- The actual root theta value in L has norm ||root||^(j^2). -/
theorem rootNormedThetaValueInL_norm
    (j : SignedLabel l.value) :
    ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ =
      (‖rootNormedElement T b‖) ^ (gaussExponent j.1) := by
  change ‖(rootNormedElement T b) ^ (gaussExponent j.1)‖ = _
  exact norm_zpow (rootNormedElement T b) (gaussExponent j.1)

/-- Exact comparison with S194 rootThetaNorm for a geometry with the same qUnit
norm. -/
theorem rootThetaNorm_eq_rootNormedElementNorm
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
    (v : V)
    (hq : ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ =
      ‖(sourceRootQUnit T b : rootBase T b)‖) :
    rootThetaNorm G v = rootNormedElementNorm T b := by
  refine (pow_left_inj₀ (n := 2 * l.value)
    (rootThetaNorm_pos G v).le (norm_nonneg _) ?_).mp ?_
  · exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  · calc
      rootThetaNorm G v ^ (2 * l.value) = ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ :=
        rootThetaNorm_pow_twoL G v
      _ = ‖(sourceRootQUnit T b : rootBase T b)‖ := hq
      _ = rootNormedElementNorm T b ^ (2 * l.value) :=
        (rootNormedElementNorm_pow_twoL T b).symm

/-- Actual root-theta L norm object connecting the root normalization to the
root tensor/L model. -/
structure RootThetaNormLObject where
  rootNorm : Real
  rootNorm_eq : rootNorm = rootNormedElementNorm T b
  rootNorm_pow_twoL : (rootNorm) ^ (2 * l.value) =
    ‖(sourceRootQUnit T b : rootBase T b)‖
  thetaValueNorm : SignedLabel l.value → Real
  thetaValueNorm_eq : thetaValueNorm = fun j =>
    ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖

/-- Actual root-theta L norm object. -/
noncomputable def rootThetaNormLObject :
    RootThetaNormLObject (l := l) T b where
  rootNorm := rootNormedElementNorm T b
  rootNorm_eq := rfl
  rootNorm_pow_twoL := rootNormedElementNorm_pow_twoL T b
  thetaValueNorm := fun j =>
    ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖
  thetaValueNorm_eq := rfl

end LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual

end
