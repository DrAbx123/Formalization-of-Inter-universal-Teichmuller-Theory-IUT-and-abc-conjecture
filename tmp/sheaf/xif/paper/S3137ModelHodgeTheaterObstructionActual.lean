import tmp.sheaf.xif.paper.S3133ModelHodgeTheaterActual
import tmp.sheaf.xif.paper.S3137ModelTheaterSkeletonActual
import LeanFormal.IUT.Audit.Status

/-! # S3137: formal obstruction — the concrete model Hodge theater cannot be a
constant theater family over the paper index (task-72)

qpilot's concrete model Hodge theater modelHodgeTheater l data is a single actual
HodgeTheater (concrete Gaussian arithmetic, model prime strip, stage4 theta packet
q = 1/5).  The from-scratch model's SourceHodgeTheaterFamily must be indexed by
the paper index (Int x Int up to lift) with a DISTINCT (injective) theater map.
A constant theater map is injective only on a subsingleton index; the paper index
is not a subsingleton.  Hence the concrete model theater gives the right FIBER
value but cannot itself be the whole family: the model needs an index-dependent
theater family (or a truncated index), exactly as recorded in the skeleton.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3137ModelHodgeTheaterObstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3133ModelHodgeTheaterActual
open LeanFormal.IUT.XiFPaper.S3133ModelVBasisActual
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual
open LeanFormal.IUT.XiFPaper.S3137ModelTheaterSkeletonActual
open LeanFormal.IUT.Audit

universe ui

/-- Two distinct paper indices exist (from non-subsingleton). -/
theorem modelIndex_exists_ne : ∃ a b : ModelIndex, a ≠ b := by
  by_contra hcon
  apply modelIndex_not_subsingleton
  refine ⟨fun a b => ?_⟩
  by_contra hab
  exact hcon ⟨a, b, hab⟩

/-- The constant theater map from the paper index to qpilot's concrete model
Hodge theater is NOT injective.  Hence the model family's theater cannot be
constant on the paper index; only a subsingleton index could carry a constant
theater family (incompatible with the paper index_equiv Int x Int). -/
theorem modelHodgeTheater_constant_not_injective (l : PrimeGeFive)
    (data : S3135ModelValueData) :
    ¬ Function.Injective (fun _ : ModelIndex => modelHodgeTheater l data) := by
  intro h
  obtain ⟨a, b, hab⟩ := modelIndex_exists_ne
  exact hab (h (a₁ := a) (a₂ := b) rfl)

end LeanFormal.IUT.XiFPaper.S3137ModelHodgeTheaterObstructionActual

namespace LeanFormal.IUT.Audit

/-- INDEX: model constant-theater obstruction (formal). -/
def S3137ModelHodgeTheaterObstructionRecord : Obligation :=
  { id := "INDEX.MODEL.constant-theater-obstruction"
    source := "qpilot S3133ModelHodgeTheaterActual (EXIT0 2477, modelHodgeTheater); S3137ModelTheaterSkeletonActual (modelIndex_not_subsingleton)"
    status := VerificationStatus.interface
    note := "FORMAL OBSTRUCTION: modelHodgeTheater_constant_not_injective — the constant map from the paper index (and its universe lift) to qpilot's concrete model Hodge theater is not injective (modelIndex_exists_ne; a constant theater family would need a subsingleton index, incompatible with index_equiv Int x Int). Therefore the model theater must be index-dependent; qpilot's concrete modelHodgeTheater supplies the right fiber value (concrete Gaussian arithmetic + modelFPrimeStrip + stage4 packet q=1/5). Not a residual; informs model assembly."
    dependsOn := ["S3133ModelHodgeTheaterActual", "S3137ModelTheaterSkeletonActual"] }

end LeanFormal.IUT.Audit