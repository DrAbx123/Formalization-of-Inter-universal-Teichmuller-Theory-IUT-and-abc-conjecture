import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HaarTranslateRealLineLogCompatibility

/-!
# Docking: the guarded decomposition on the real-line dilation contraction carrier

Task `hunit-epsilon-transfer-20261016`, report section 20, docking evaluation of
the carrier-line section 16 interface request block
(`HaarTranslateRealLineLogCompatibility`, SHA
3E35E8F7C19539D4FB4831109445A189C5BDB3D09CE2D0B56CFDE14E2DF41E70) against the
guarded decomposition interface of `CardHullRealGeneratorNonpositivity.lean`.

Consumed signatures of the request block: signature 8
(`realLineDilationLogWeight` with `_mul`, `_neg`, `_half`) and signature 9
(`realLineLogShellLogVolume_dilation`).  On the contraction submonoid
`{t | t != 0 and |t| <= 1}` of the multiplicative real line, the guarded
interface `LogVolumeScaleDecompositionNonempty` is instantiated with `logVolume`
the supremum of the log weights over the parameter set, `logScale` the log
weight `log |t|`, and `unitRegion = {1}`.  The instance is nondegenerate: the
explicit contracting dilation `1/2` carries the strictly negative factor
`-log 2`, in contrast with the empty-set degeneracy of the unguarded section 19
interface.  The singleton reading
`logVolume {t} = log(mu(t . O))` consumes the normalized Haar dilation law
(signatures 5-9 composed through `realLineLogShellLogVolume_dilation`), making
the measure half and the weight half of the request block meet in one statement.

Boundary: this is a test-carrier docking, not the paper's log-volume; R9 body
is untouched, and the local-field / residue-degree items of the request block
remain open (report section 20 field list).  The carrier is the multiplicative
line, not the paper's `1,circ U`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

open MeasureTheory

open scoped Pointwise

namespace HaarTranslateModel.RealLine

/-- The contraction submonoid of the multiplicative real line: nonzero
dilations of modulus at most one.  This is the test carrier on which the log
weight `log |t|` is nonpositive and the guarded decomposition becomes
nondegenerate. -/
def dilationContractionSubmonoid : Submonoid Real where
  carrier := {t | t ≠ 0 ∧ |t| ≤ 1}
  one_mem' := ⟨one_ne_zero, le_of_eq abs_one⟩
  mul_mem' := by
    rintro x y ⟨hx0, hx1⟩ ⟨hy0, hy1⟩
    refine ⟨mul_ne_zero hx0 hy0, ?_⟩
    rw [abs_mul]
    exact mul_le_one₀ hx1 (abs_nonneg y) hy1

/-- **The guarded decomposition instantiated on the contraction carrier.**
Regions are measured by the supremum of the log weights `log |t|` of their
dilation parameters; the factor is the log weight itself; the unit region is
`{1}`, normalized by `log 1 = 0`.  The decomposition law is the suprema
translation law fed by the multiplicativity `realLineDilationLogWeight_mul` of
the section 16 request block. -/
def dilationContractionLogVolumeScaleDecomposition :
    LogVolumeScaleDecompositionNonempty ↥dilationContractionSubmonoid where
  logVolume := fun A => sSup (realLineDilationLogWeight '' ((↑) '' A))
  unitRegion := {1}
  unitRegion_nonempty := Set.singleton_nonempty 1
  normalization := by
    have h1 : realLineDilationLogWeight (1 : Real) = 0 := by
      rw [realLineDilationLogWeight, abs_one, Real.log_one]
    rw [Set.image_singleton, Set.image_singleton, Submonoid.coe_one, h1,
      csSup_singleton]
  logScale := fun t => realLineDilationLogWeight (↑t)
  decomposition := by
    intro x A hA
    have hne : (realLineDilationLogWeight '' ((↑) '' A)).Nonempty := by
      obtain ⟨a, ha⟩ := hA
      exact ⟨realLineDilationLogWeight (↑a), ↑a, ⟨a, ha, rfl⟩, rfl⟩
    have hbdd : BddAbove (realLineDilationLogWeight '' ((↑) '' A)) := by
      refine ⟨0, ?_⟩
      rintro y ⟨b, ⟨a, ha, rfl⟩, rfl⟩
      exact (Real.log_nonpos_iff (abs_nonneg (↑a))).mpr a.2.2
    have himg : realLineDilationLogWeight ''
          ((↑) '' ((fun a => a * x) '' A)) =
        (fun y : Real => y + realLineDilationLogWeight (↑x)) ''
          (realLineDilationLogWeight '' ((↑) '' A)) := by
      ext y
      constructor
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨a, ha, rfl⟩ := hb
        obtain ⟨a', ha', rfl⟩ := ha
        refine ⟨realLineDilationLogWeight (↑a'),
          ⟨↑a', ⟨a', ha', rfl⟩, rfl⟩, ?_⟩
        rw [Submonoid.coe_mul,
          realLineDilationLogWeight_mul (↑a') (↑x) a'.2.1 x.2.1]
      · rintro ⟨s, hs, hs_eq⟩
        obtain ⟨b, hb, rfl⟩ := hs
        obtain ⟨a, ha, rfl⟩ := hb
        refine ⟨↑(a * x), ⟨a * x, ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
        rw [Submonoid.coe_mul,
          realLineDilationLogWeight_mul (↑a) (↑x) a.2.1 x.2.1]
        exact hs_eq
    change sSup (realLineDilationLogWeight ''
        ((↑) '' ((fun a => a * x) '' A))) =
      sSup (realLineDilationLogWeight '' ((↑) '' A)) +
        realLineDilationLogWeight (↑x)
    rw [himg]
    exact real_sSup_image_add_const hne hbdd _

/-- The factor of the contraction instance is the log weight `log |t|`. -/
theorem dilationContractionLogVolumeScaleDecomposition_logScale_eq
    (t : ↥dilationContractionSubmonoid) :
    dilationContractionLogVolumeScaleDecomposition.logScale t =
      realLineDilationLogWeight (↑t) :=
  rfl

/-- The factor is nonpositive on the whole contraction carrier. -/
theorem dilationContractionLogVolumeScaleDecomposition_logScale_nonpos
    (t : ↥dilationContractionSubmonoid) :
    dilationContractionLogVolumeScaleDecomposition.logScale t ≤ 0 := by
  rw [dilationContractionLogVolumeScaleDecomposition_logScale_eq t]
  exact (Real.log_nonpos_iff (abs_nonneg (↑t))).mpr t.2.2

/-- **Nondegeneracy of the guarded interface.**  On contracting dilations the
factor is strictly negative: unlike the unguarded section 19 interface (whose
factor is forced to vanish), the guarded structure carries a genuinely negative
`dot-mu-log`. -/
theorem dilationContractionLogVolumeScaleDecomposition_logScale_neg
    (t : ↥dilationContractionSubmonoid) (ht : |(t : Real)| < 1) :
    dilationContractionLogVolumeScaleDecomposition.logScale t < 0 :=
  realLineDilationLogWeight_neg (↑t) (abs_pos.mpr t.2.1) ht

/-- The additivity law of the guarded structure, instantiated on the
contraction carrier. -/
theorem dilationContractionLogVolumeScaleDecomposition_logScale_mul
    (t u : ↥dilationContractionSubmonoid) :
    dilationContractionLogVolumeScaleDecomposition.logScale (t * u) =
      dilationContractionLogVolumeScaleDecomposition.logScale t +
        dilationContractionLogVolumeScaleDecomposition.logScale u :=
  LogVolumeScaleDecompositionNonempty.logScale_mul
    dilationContractionLogVolumeScaleDecomposition t u

/-- The explicit contracting dilation `1/2`. -/
def dilationContractionHalf : ↥dilationContractionSubmonoid :=
  ⟨ 1 / 2, by
      constructor
      · norm_num
      · rw [abs_of_pos (by norm_num : (0 : Real) < 1 / 2)]
        norm_num⟩

theorem dilationContractionHalf_val :
    (dilationContractionHalf : Real) = 1 / 2 :=
  rfl

/-- The explicit negative step value: the guarded instance evaluates to
`-log 2` at the contracting dilation `1/2` (the request block's test step). -/
theorem dilationContractionHalf_logScale_eq :
    dilationContractionLogVolumeScaleDecomposition.logScale dilationContractionHalf =
      -Real.log 2 :=
  realLineDilationLogWeight_half

/-- The explicit nonvanishing witness: the guarded instance has a strictly
negative factor at `1/2`. -/
theorem dilationContractionHalf_logScale_neg :
    dilationContractionLogVolumeScaleDecomposition.logScale dilationContractionHalf < 0 :=
  dilationContractionLogVolumeScaleDecomposition_logScale_neg
    dilationContractionHalf
    (by rw [dilationContractionHalf_val, abs_of_pos (by norm_num : (0 : Real) < 1 / 2)]
        norm_num)

/-- **Singleton reading: the measure half and the weight half meet.**  The
log-volume of the singleton parameter `{t}` equals the signed log-volume of the
dilated log-shell `t . O` under the normalized Haar measure, consuming
signature 9 of the section 16 request block. -/
theorem dilationContractionLogVolumeScaleDecomposition_logVolume_singleton_eq_logShell
    (t : ↥dilationContractionSubmonoid) :
    dilationContractionLogVolumeScaleDecomposition.logVolume {t} =
      Real.log (normalizedRealLineVolume ((↑t) • unitInterval)).toReal := by
  have h1 : dilationContractionLogVolumeScaleDecomposition.logVolume {t} =
      realLineDilationLogWeight (↑t) := by
    change sSup (realLineDilationLogWeight ''
        ((↑) '' ({t} : Set ↥dilationContractionSubmonoid))) =
      realLineDilationLogWeight (↑t)
    rw [Set.image_singleton, Set.image_singleton, csSup_singleton]
  rw [h1]
  exact (realLineLogShellLogVolume_dilation (↑t)).symm

end HaarTranslateModel.RealLine

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the docking of the guarded decomposition onto the
real-line dilation contraction carrier (carrier-line report section 16 request
block, signatures 8 and 9). -/
def cardHullRealHaarDilationDocking : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-haar-dilation-docking"
    source :=
      "[AbsTopIII] Proposition 5.7, (i), (b) (corpus lines 7915-7941); " ++
        "carrier-line report section 16 interface request block " ++
        "(HaarTranslateRealLineLogCompatibility, SHA 3E35E8F7...), " ++
        "signatures 8 and 9"
    status := VerificationStatus.interface
    note :=
      "Guarded LogVolumeScaleDecompositionNonempty instantiated on the " ++
        "dilation contraction submonoid {t | t != 0, |t| <= 1}: logVolume = " ++
        "sup of realLineDilationLogWeight over the parameter set, logScale = " ++
        "log |t|, unitRegion = {1}. Consumes realLineDilationLogWeight_mul, " ++
        "_neg, _half and realLineLogShellLogVolume_dilation of the request " ++
        "block. Nondegeneracy: logScale(1/2) = -log 2 < 0, in contrast with " ++
        "the empty-set degeneracy of the unguarded interface. Singleton " ++
        "reading ties logVolume {t} to log(mu(t . O)). NOT the paper carrier; " ++
        "R9 body untouched; residue-degree/local-field items of the request " ++
        "block open."
    dependsOn :=
      [ "IUT-III.corollary-3.12-card-hullreal-generator-nonpositivity" ] }

end LeanFormal.IUT.Audit
