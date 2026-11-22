/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.takkun.IutLean.Theta.ThetaValues
import tmp.sheaf.takkun.IutLean.Padic.LogVolume
import tmp.sheaf.takkun.IutLean.Padic.LogShellRadius
import tmp.sheaf.takkun.IutLean.Padic.ShellTransport
import tmp.sheaf.takkun.IutLean.Arithmetic.RealKummer
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperThetaRootObstructionActual
import tmp.sheaf.xif.paper.ThetaHullActual

/-!
# O2ThetaObjectActual — O2 Theta-pilot object (A501 object-first rebuild)

Object-only construction, no comparisons.  Sources of every field:

* `Vbad`: the finite bad locus `Bad (nativePlaceSelection T)` (source data);
* `qroot`: the `2ℓ`-layer of the actual root system: `sourceRoot T b`
  (`PaperThetaRootObstructionActual.sourceRootSystem` = `algClosedRootSystem q`,
  the same all-order root chain as TAKKUN `realQRootSystem`/`rootSystemOfAlgClosed`),
  with `qroot^(2ℓ) = q` (`rootNormedElement_L_pow`);
* `thetaValue j`: TAKKUN `IUT.Theta.thetaValueMon qroot j = qroot^{j²}`
  (`thetaValueMon`, `gaussExp`, `thetaValueMon_neg` for the ±1 symmetry);
* `thetaLogVolume j`: the INDEPENDENT formula `gaussExp j * logVol(qroot)`
  (not `q/(2ℓ)`; cf. TAKKUN `IUT.Padic.logVol_pow`), proved equal to
  `Real.log ‖thetaValue j‖` (`thetaPilotLogVolume_eq_log_norm`);
* `globalThetaLogVolume`: `∑ b` over V_bad of the per-place read volume;
* hull constants: TAKKUN `IUT.Padic.aRadius/bRadius` (IUT-IV constants),
  `IUT.Padic.shell`/`shell_subset_iff`/`unit_mul_shell` (λ·O inclusion and
  unit-invariance of the log-shell).

No q/(2ℓ) definition, no comparison, no interface, no incomplete proof. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.O2ThetaObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open scoped BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual `2ℓ`-th root of q at a bad place, in the root extension `L_b`. -/
noncomputable def qroot (b : Bad (nativePlaceSelection T)) : rootNormedExtension T b :=
  ⟨rootNormedElement T b, rootNormedElement_mem T b⟩

/-- Provenance from the actual root SYSTEM: `qroot` is the `2ℓ`-layer `sourceRoot`
(the same all-order root chain as TAKKUN `rootSystemOfAlgClosed`). -/
theorem qroot_eq_rootSystem_twoL (b : Bad (nativePlaceSelection T)) :
    qroot T b =
      (⟨(sourceRoot T b : rootNormedAmbient T b), rootNormedElement_mem T b⟩ :
        rootNormedExtension T b) := rfl

/-- Root equation `qroot^(2ℓ) = q`. -/
theorem qroot_pow (b : Bad (nativePlaceSelection T)) :
    (qroot T b) ^ (2 * l.value) =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        ((qVFamily T b).q : rootBase T b) := by
  unfold qroot
  simpa [sourceRootQUnit] using rootNormedElement_L_pow (T := T) b

/-- Theta value: TAKKUN `thetaValueMon qroot j` (`= qroot^{j²}`) in `L_b`. -/
noncomputable def thetaPilotValue (j : SignedLabel l.value) : S1902Carrier T :=
  fun b =>
    ((IUT.Theta.thetaValueMon (rootNormedUnit T b) j.1 :
      (rootNormedExtension T b)ˣ) : rootNormedExtension T b)

/-- Definitional form: the theta value is `qroot` to the `gaussExp j` power. -/
theorem thetaPilotValue_def (j : SignedLabel l.value)
    (b : Bad (nativePlaceSelection T)) :
    thetaPilotValue T j b = (qroot T b) ^ (IUT.Theta.gaussExp j.1).toNat := by
  simp [thetaPilotValue, IUT.Theta.thetaValueMon, qroot, rootNormedUnit]

/-- `±1` symmetry: `thetaValue (−j) = thetaValue j` (TAKKUN `thetaValueMon_neg`). -/
theorem thetaPilotValue_neg (j : SignedLabel l.value) :
    thetaPilotValue T (SignedLabel.neg j) = thetaPilotValue T j := by
  funext b
  simp [thetaPilotValue, IUT.Theta.thetaValueMon_neg]

/-- The `2ℓ`-th power of the theta value is the corresponding q-power. -/
theorem thetaPilotValue_pow (j : SignedLabel l.value)
    (b : Bad (nativePlaceSelection T)) :
    (thetaPilotValue T j b) ^ (2 * l.value) =
      ((qroot T b) ^ (2 * l.value)) ^ (IUT.Theta.gaussExp j.1).toNat := by
  rw [thetaPilotValue_def, ← pow_mul, mul_comm, pow_mul]

/-- The local q-root log-volume `logVol(qroot)` in `L_b`. -/
noncomputable def localQrootLogVolume (b : Bad (nativePlaceSelection T)) : Real :=
  Real.log ‖(qroot T b : rootNormedExtension T b)‖

/-- The INDEPENDENT Theta read volume: `gaussExp j * logVol(qroot)` (no q/(2ℓ)). -/
noncomputable def thetaPilotLogVolume (j : SignedLabel l.value)
    (b : Bad (nativePlaceSelection T)) : Real :=
  ((IUT.Theta.gaussExp j.1).toNat : Real) * localQrootLogVolume T b

/-- The independent formula equals the log-norm of the theta value (cf. TAKKUN
`IUT.Padic.logVol_pow`; here for the root-extension norm). -/
theorem thetaPilotLogVolume_eq_log_norm (j : SignedLabel l.value)
    (b : Bad (nativePlaceSelection T)) :
    thetaPilotLogVolume T j b =
      Real.log ‖(thetaPilotValue T j b : rootNormedExtension T b)‖ := by
  unfold thetaPilotLogVolume localQrootLogVolume
  rw [thetaPilotValue_def, norm_pow, Real.log_pow]
  ring

/-- The cast of `gaussExp` from `toNat` form (for the `j² * logVol` reading). -/
theorem gaussExp_toNat_cast (j : Int) :
    ((IUT.Theta.gaussExp j).toNat : Real) = (IUT.Theta.gaussExp j : Real) := by
  have h := IUT.Theta.gaussExp_nonneg j
  have hz : ((IUT.Theta.gaussExp j).toNat : Int) = IUT.Theta.gaussExp j :=
    Int.toNat_of_nonneg h
  exact_mod_cast hz

/-- The `gaussExp j * logVol(qroot)` reading of the independent Theta volume. -/
theorem thetaPilotLogVolume_eq_gaussExp_mul (j : SignedLabel l.value)
    (b : Bad (nativePlaceSelection T)) :
    thetaPilotLogVolume T j b =
      (IUT.Theta.gaussExp j.1 : Real) * localQrootLogVolume T b := by
  unfold thetaPilotLogVolume
  rw [gaussExp_toNat_cast]

/-- The finite bad locus. -/
def Vbad [Fintype (Bad (nativePlaceSelection T))] :
    Finset (Bad (nativePlaceSelection T)) := Finset.univ

/-- Global Theta read volume: sum over V_bad. -/
noncomputable def globalThetaLogVolume [Fintype (Bad (nativePlaceSelection T))]
    (j : SignedLabel l.value) : Real :=
  ∑ b : Bad (nativePlaceSelection T), thetaPilotLogVolume T j b


/-- The local Theta read volume averaged over the canonical signed-label procession. -/
noncomputable def localThetaLogVolume_average (b : Bad (nativePlaceSelection T)) : Real :=
  (XiFPaperThetaHull.canonicalProcession (l := l)).average
    (fun j : SignedLabel l.value => thetaPilotLogVolume T j b)

/-- The average of the local read volumes is `logVol(qroot)` times the average of
`gaussExp` over the procession labels. -/
theorem localThetaLogVolume_average_eq (b : Bad (nativePlaceSelection T)) :
    localThetaLogVolume_average T b =
      localQrootLogVolume T b *
        (XiFPaperThetaHull.canonicalProcession (l := l)).average
          (fun j : SignedLabel l.value => ((IUT.Theta.gaussExp j.1).toNat : Real)) := by
  unfold localThetaLogVolume_average thetaPilotLogVolume
  rw [show (fun j : SignedLabel l.value =>
        ((IUT.Theta.gaussExp j.1).toNat : Real) * localQrootLogVolume T b) =
      (fun j : SignedLabel l.value =>
        localQrootLogVolume T b * ((IUT.Theta.gaussExp j.1).toNat : Real)) by
    funext j
    ring]
  rw [XiFPaperThetaHull.FiniteProcession.average_smul]

/-- The global Theta read volume averaged over the canonical procession:
local average at each bad place, then summed over V_bad. -/
noncomputable def globalThetaLogVolume_average : Real :=
  ∑ b : Bad (nativePlaceSelection T), localThetaLogVolume_average T b

/-- The global average equals the procession average of the global read volume. -/
theorem globalThetaLogVolume_average_eq :
    globalThetaLogVolume_average T =
      (XiFPaperThetaHull.canonicalProcession (l := l)).average
        (fun j : SignedLabel l.value => globalThetaLogVolume T j) := by
  unfold globalThetaLogVolume_average localThetaLogVolume_average globalThetaLogVolume
  simp only [XiFPaperThetaHull.FiniteProcession.average]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

/-- The global q-root log-volume: sum of `logVol(qroot)` over V_bad. -/
noncomputable def globalQrootLogVolume : Real :=
  ∑ b : Bad (nativePlaceSelection T), localQrootLogVolume T b

/-- Global normalization: the global Theta read volume is `gaussExp j` times the
global q-root log-volume (per bad place summed exactly). -/
theorem globalThetaLogVolume_eq_qrootGlobal (j : SignedLabel l.value) :
    globalThetaLogVolume T j =
      ((IUT.Theta.gaussExp j.1).toNat : Real) * globalQrootLogVolume T := by
  unfold globalThetaLogVolume globalQrootLogVolume thetaPilotLogVolume
  rw [Finset.mul_sum]

/-- The procession-averaged global read volume is the global q-root log-volume
times the procession average of `gaussExp`. -/
theorem globalThetaLogVolume_average_eq_qrootGlobal :
    globalThetaLogVolume_average T =
      globalQrootLogVolume T *
        (XiFPaperThetaHull.canonicalProcession (l := l)).average
          (fun j : SignedLabel l.value => ((IUT.Theta.gaussExp j.1).toNat : Real)) := by
  unfold globalThetaLogVolume_average globalQrootLogVolume
  calc ∑ b : Bad (nativePlaceSelection T), localThetaLogVolume_average T b
      = ∑ b : Bad (nativePlaceSelection T), localQrootLogVolume T b *
          (XiFPaperThetaHull.canonicalProcession (l := l)).average
            (fun j : SignedLabel l.value => ((IUT.Theta.gaussExp j.1).toNat : Real)) := by
        apply Finset.sum_congr rfl
        intro b _
        exact localThetaLogVolume_average_eq T b
    _ = (∑ b : Bad (nativePlaceSelection T), localQrootLogVolume T b) *
          (XiFPaperThetaHull.canonicalProcession (l := l)).average
            (fun j : SignedLabel l.value => ((IUT.Theta.gaussExp j.1).toNat : Real)) := by
        rw [Finset.sum_mul]
/-- The global read volume is the sum of the log-norms of the theta values. -/
theorem globalThetaLogVolume_eq [Fintype (Bad (nativePlaceSelection T))]
    (j : SignedLabel l.value) :
    globalThetaLogVolume T j =
      ∑ b : Bad (nativePlaceSelection T),
        Real.log ‖(thetaPilotValue T j b : rootNormedExtension T b)‖ := by
  unfold globalThetaLogVolume
  exact Finset.sum_congr rfl fun b _ => thetaPilotLogVolume_eq_log_norm T j b

/-! ### Hull constants (TAKKUN IUT-IV constants and log-shell sets) -/

section HullConstants
variable (p e : Nat) [Fact p.Prime]

/-- IUT-IV hull radius constants `(a_i, b_i)` (TAKKUN `aRadius`, `bRadius`). -/
def hullRadii : Real × Real := (IUT.Padic.aRadius p e, IUT.Padic.bRadius p e)

/-- Tame values of the hull radii. -/
theorem hullRadii_tame (hp : 2 < p) (he : 1 <= e) (h : e + 2 <= p) :
    hullRadii p e = (1 / (e : Real), -(1 / (e : Real))) := by
  unfold hullRadii
  rw [IUT.Padic.radius_tame hp he h]

/-- The actual log-shell set `S_λ = {x | ‖x‖ ≤ p^{-λ}}` (TAKKUN `shell`). -/
def hullShell (lam : Int) : Set ℚ_[p] := IUT.Padic.shell p lam

/-- Shell inclusion faithfully reflects the exponent order (`shell_subset_iff`). -/
theorem hullShell_subset_iff {lam mu : Int} :
    hullShell p lam ⊆ hullShell p mu ↔ mu <= lam :=
  IUT.Padic.shell_subset_iff (p := p)

/-- Unit multiplication preserves the log-shell (`unit_mul_shell`). -/
theorem hullShell_unit_mul {c : ℚ_[p]} (hc : ‖c‖ = 1) {lam : Int} {x : ℚ_[p]}
    (hx : x ∈ hullShell p lam) : c * x ∈ hullShell p lam :=
  IUT.Padic.unit_mul_shell (p := p) hc hx


/-- The `dim * log p` scaling law of the local log-volume (TAKKUN logVol_p_pow):
the normalized volume of the shell `p^n Z_p` is `-n * log p`. -/
theorem hullLogVolume_p_pow (n : Nat) :
    IUT.Padic.logVol ((p : ℚ_[p]) ^ n) = -(n : Real) * Real.log (p : Real) :=
  IUT.Padic.logVol_p_pow n
end HullConstants

/-! ### The object -/

/-- O2 Theta-pilot object (object-only; no comparisons). -/
structure O2ThetaObject [Fintype (Bad (nativePlaceSelection T))] where
  Vbad : Finset (Bad (nativePlaceSelection T))
  qroot : ∀ b, rootNormedExtension T b
  qroot_rootSystem_twoL : ∀ b, qroot b =
    (⟨(sourceRoot T b : rootNormedAmbient T b), rootNormedElement_mem T b⟩ :
      rootNormedExtension T b)
  thetaValue : SignedLabel l.value → S1902Carrier T
  thetaValue_thetaValueMon : ∀ j, thetaValue j = thetaPilotValue T j
  thetaValue_pow : ∀ j b, (thetaValue j b) ^ (2 * l.value) =
    ((qroot b) ^ (2 * l.value)) ^ (IUT.Theta.gaussExp j.1).toNat
  thetaLogVolume : SignedLabel l.value → Real
  thetaLogVolume_eq : ∀ j, thetaLogVolume j = globalThetaLogVolume T j

/-- The constructed O2 object. -/
noncomputable def o2ThetaObject [Fintype (Bad (nativePlaceSelection T))] :
    O2ThetaObject T where
  Vbad := Vbad T
  qroot := qroot T
  qroot_rootSystem_twoL := qroot_eq_rootSystem_twoL T
  thetaValue := thetaPilotValue T
  thetaValue_thetaValueMon := fun _ => rfl
  thetaValue_pow := thetaPilotValue_pow T
  thetaLogVolume := globalThetaLogVolume T
  thetaLogVolume_eq := fun _ => rfl

/-- `_constructed`: every field is the fixed real definition above. -/
theorem o2ThetaObject_constructed [Fintype (Bad (nativePlaceSelection T))] :
    (o2ThetaObject T).Vbad = Vbad T ∧
    (o2ThetaObject T).qroot = qroot T ∧
    (o2ThetaObject T).thetaValue = thetaPilotValue T ∧
    (o2ThetaObject T).thetaLogVolume = globalThetaLogVolume T := by
  refine ⟨rfl, rfl, rfl, rfl⟩

#check o2ThetaObject_constructed
#check thetaPilotLogVolume_eq_log_norm
#check thetaPilotLogVolume_eq_gaussExp_mul
#check hullRadii_tame
#check hullShell_subset_iff

end LeanFormal.IUT.XiFPaper.O2ThetaObjectActual
end
