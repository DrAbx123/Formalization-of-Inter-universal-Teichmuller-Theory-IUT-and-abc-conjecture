import tmp.sheaf.xif.paper.S2027LocalArtinActual

/-!
# S2048: transfer compatibility for the local reciprocity datum

Layer: **O** (original Theta-link / q-pilot).  Consumer: S2024's
LocalReciprocityData.transfer_compat, hence S2017's muQZComparison and
muHatComparison through muQZComparison_of_data.

## The statement

Let G_v = Gal(Qbar_p / Q_p), let H <= K be open subgroups, and let
L_U = FixedField U.  S2024 records the local reciprocity datum on torsion as

  equiv U : torsion (Ab U) ~= torsion (L_U)^x

together with the transfer square

  equiv H (V_{K/H} v) = incl (equiv K v),   V_{K/H} : Ab K -> Ab H,

where incl : torsion (L_K)^x -> torsion (L_H)^x is the inclusion of the roots
of unity of the smaller fixed field into those of the larger one.  In local
class field theory this is the standard functoriality of the local Artin map:
for rec_U : torsion (L_U)^x -> torsion (Ab U) (the inverse of equiv U), the
square is

  V_{K/H} o rec_K = rec_H o incl.

This file isolates that square, proves that it is exactly the field consumed
by S2024's colimit (stageHom_toStage and its converse), and constructs the
datum from a local Artin family together with the square.

## What this file proves (unconditional, no sorry, no axiom)

1. TransferCompat e and ArtinTransferCompat r: the abstract-carrier and
   source-level forms of the transfer square.
2. transferCompat_iff_artin: for e = r.symm the two forms are equivalent.
   This is the precise sense in which the field of S2024 is the usual
   Ver o rec = rec o incl compatibility.
3. transferCompat_iff_ambient: the square can be checked after embedding both
   sides into torsion (Qbar_p)^x, where the inclusion side becomes equality of
   ambient roots of unity.  This uses S2024's
   torsionUnitsMap_val_comp_inclusion and injectivity of the ambient
   embedding.
4. transferCompat_iff_stage: the square is equivalent to compatibility of the
   stage maps stageHom with the transfer toStage.  S2024 proved the forward
   direction (stageHom_toStage); the converse is proved here, so the field is
   not merely sufficient for the colimit but necessary.
5. fixedFieldTorsionUnitsInclusion_refl and _comp: the inclusion side is
   reflexive and compatible with composition of subgroup inclusions.
6. Filling the field: localReciprocityDataOfArtin and
   localReciprocityDataOfSource build LocalReciprocityData p from a local
   Artin family (or from S2027's LocalArtinSourceData) plus exactly the
   square.
7. localReciprocityDataMissing_iff_artinSource: S2024's missing datum is
   equivalent to the existence of a local Artin family satisfying the
   transfer square.  The first missing in dependency order is the family
   itself (M2a); the square is the second, independent input (M2b).

## The exact first missing (not assumed, not faked)

The file constructs no local Artin map.  The first missing input is a family

  rec U : torsion (L_U)^x ~= torsion (Ab U)

for all open U, together with the transfer square.  Neither Mathlib v4.32.2
nor this Lake project contains the local Artin map for finite extensions of
Q_p: lakefile.toml has no dependency on a local class field theory library,
and the tree has only the abstract Abelianization and the concrete fixed
fields.  S2027 records the same gap as LocalArtinSourceData; its htransfer
hypothesis is definitionally the SourceTransferCompat predicate below.  Thus
S2027 together with this file is a conditional reduction: LocalArtinSourceData
(M2a + the abstract-vs-profinite comparison M2c) plus SourceTransferCompat
(M2b) constructs S2024's datum, and conversely every S2024 datum gives a local
Artin family with the square.  The reduction is not an inhabitant.

A full local CFT development exists in the workspace as untracked reference
material at tmp/local-cft-port/local-class-field-theory-main/, and its
PadicField.artin_transfer
(LocalClassFieldTheory/Brauer/ArtinTransfer.lean, around line 246) proves
exactly the finite-level transfer square.  It is not a dependency of this
project: it is pinned to Lean v4.32.0 and is not in lakefile.toml or
lake-manifest.json.  Therefore the precise first missing here is the port of
that Artin map/transfer theorem into this tree, not a mathematical gap in the
formal square below.  No declaration in this file assumes that port.

## Not run

Full Project build, target comparator, independent review, and the port of the
external local CFT library were not run.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false

noncomputable section
open scoped DirectSum
open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual

namespace LeanFormal.IUT.XiFPaper.S2048TransferCompatActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. The torsion units of the fixed fields -/

/-- The roots of unity of the fixed field L_U = FixedField U, written in the
same form as S2027's mu. -/
abbrev mu (U : Index p) : Type :=
  S2027LocalArtinActual.mu p U

/-- The roots of unity of L_U embedded in the roots of unity of Qbar_p. -/
noncomputable def muInGlobal (U : Index p) :
    mu p U →* CommGroup.torsion (AlgebraicClosure ℚ_[p])ˣ :=
  RationalCircleCyclotome.torsionUnitsMap
    (LocalIntegralUnitKummerInjectivity.FixedField p U).val.toRingHom

/-! ## 2. The two forms of the transfer square -/

/-- A local Artin map on torsion for every open subgroup, in the direction
mu(L_U) -> (Ab U)_tors.  This is the first missing input (M2a); no inhabitant
is constructed in this file. -/
structure LocalArtinTorsionMap (p : Nat) [Fact (Nat.Prime p)] : Type where
  /-- The local Artin map on torsion, for every open subgroup. -/
  artin : forall U : Index p, mu p U ≃* CommGroup.torsion (Abelianization U)

/-- **The abstract-carrier transfer square.**  For a family of levelwise
reciprocity equivalences e, the Verlagerung Ab K -> Ab H corresponds to the
inclusion of the roots of unity of the two fixed fields.  This is exactly the
transfer_compat field of S2024's LocalReciprocityData. -/
def TransferCompat
    (e : forall U : Index p,
      CommGroup.torsion (Abelianization U) ≃* mu p U) : Prop :=
  forall {H K : Index p} (h : H <= K)
    (v : CommGroup.torsion (Abelianization K)),
    e H (torsionMap (verlagerungOpen p h) v) =
      fixedFieldTorsionUnitsInclusion p h (e K v)

/-- **The source-level transfer square.**  A local Artin family
rec U : torsion (L_U)^x -> torsion (Ab U) satisfies
Ver o rec_K = rec_H o incl.  This is the form in which local class field
theory states the compatibility of the reciprocity map with the transfer. -/
def ArtinTransferCompat (r : LocalArtinTorsionMap p) : Prop :=
  forall {H K : Index p} (h : H <= K) (x : mu p K),
    torsionMap (verlagerungOpen p h) (r.artin K x) =
      r.artin H (fixedFieldTorsionUnitsInclusion p h x)

/-- The two forms of the transfer square agree: if e = r.symm, the
abstract-carrier square for e is the source-level square for r. -/
theorem transferCompat_iff_artin (r : LocalArtinTorsionMap p) :
    TransferCompat p (fun U => (r.artin U).symm) ↔
      ArtinTransferCompat p r := by
  constructor
  . intro hc H K h x
    have h := hc h (r.artin K x)
    simpa using congrArg (fun y => r.artin H y) h
  . intro hc H K h v
    apply (r.artin H).injective
    simp only [MulEquiv.apply_symm_apply]
    have hx := hc h ((r.artin K).symm v)
    simpa using hx

/-- Filling S2024's transfer_compat field from a local Artin family and the
source-level square. -/
noncomputable def localReciprocityDataOfArtin (r : LocalArtinTorsionMap p)
    (hc : ArtinTransferCompat p r) : LocalReciprocityData p where
  equiv := fun U => (r.artin U).symm
  transfer_compat := (transferCompat_iff_artin p r).mpr hc

/-- Every S2024 datum gives a local Artin family on torsion: this is just the
inverse of its levelwise equivalence. -/
noncomputable def artinOfData (data : LocalReciprocityData p) :
    LocalArtinTorsionMap p where
  artin := fun U => (data.equiv U).symm

/-- The inverse family obtained from S2024's datum satisfies the source-level
transfer square.  This is the converse of localReciprocityDataOfArtin at the
level of the square. -/
theorem artinTransferCompat_of_data (data : LocalReciprocityData p) :
    ArtinTransferCompat p (artinOfData p data) := by
  intro H K h x
  have hsq := data.transfer_compat h ((data.equiv K).symm x)
  calc
    torsionMap (verlagerungOpen p h) ((data.equiv K).symm x) =
        (data.equiv H).symm ((data.equiv H)
          (torsionMap (verlagerungOpen p h) ((data.equiv K).symm x))) :=
      ((data.equiv H).symm_apply_apply _).symm
    _ = (data.equiv H).symm
          (fixedFieldTorsionUnitsInclusion p h
            ((data.equiv K) ((data.equiv K).symm x))) := by rw [hsq]
    _ = (data.equiv H).symm
          (fixedFieldTorsionUnitsInclusion p h x) := by
      rw [MulEquiv.apply_symm_apply]

/-- **S2024's missing datum is exactly a local Artin family with the transfer
square.**  This decomposes the missing input into (M2a) the family and (M2b)
the square; it introduces no inhabitant. -/
theorem localReciprocityDataMissing_iff_artinSource :
    localReciprocityDataMissing p ↔
      exists r : LocalArtinTorsionMap p, ArtinTransferCompat p r := by
  constructor
  . rintro ⟨data⟩
    exact ⟨artinOfData p data, artinTransferCompat_of_data p data⟩
  . rintro ⟨r, hc⟩
    exact ⟨localReciprocityDataOfArtin p r hc⟩

/-- The first missing input in dependency order: a family of local Artin maps
on torsion.  This is (M2a); it is stated, not assumed. -/
def localArtinTorsionMissing : Prop :=
  Nonempty (LocalArtinTorsionMap p)

/-- S2024's datum supplies the first missing input. -/
theorem localArtinTorsionMissing_of_dataMissing
    (h : localReciprocityDataMissing p) : localArtinTorsionMissing p := by
  obtain ⟨data⟩ := h
  exact ⟨artinOfData p data⟩

/-! ## 3. The ambient form in Qbar_p -/

/-- The transfer square checked after embedding the two roots of unity into
Qbar_p.  The inclusion mu(L_K) -> mu(L_H) becomes equality of the ambient
roots. -/
def AmbientTransferCompat
    (e : forall U : Index p,
      CommGroup.torsion (Abelianization U) ≃* mu p U) : Prop :=
  forall {H K : Index p} (h : H <= K)
    (v : CommGroup.torsion (Abelianization K)),
    muInGlobal p H (e H (torsionMap (verlagerungOpen p h) v)) =
      muInGlobal p K (e K v)

/-- **The square is equivalent to its ambient form.**  The forward direction
uses S2024's torsionUnitsMap_val_comp_inclusion; the converse uses
injectivity of the embedding of a fixed field's roots of unity into Qbar_p. -/
theorem transferCompat_iff_ambient
    (e : forall U : Index p,
      CommGroup.torsion (Abelianization U) ≃* mu p U) :
    TransferCompat p e ↔ AmbientTransferCompat p e := by
  constructor
  . intro hc H K h v
    rw [hc h v]
    exact congrArg (fun f => f (e K v))
      (torsionUnitsMap_val_comp_inclusion p h)
  . intro hc H K h v
    apply torsionUnitsMap_injective
      (LocalIntegralUnitKummerInjectivity.FixedField p H).val.toRingHom
      (fun a b hab => Subtype.ext hab)
    change muInGlobal p H (e H (torsionMap (verlagerungOpen p h) v)) =
      muInGlobal p H (fixedFieldTorsionUnitsInclusion p h (e K v))
    rw [hc h v]
    exact (congrArg (fun f => f (e K v))
      (torsionUnitsMap_val_comp_inclusion p h)).symm

/-! ## 4. The stage-map form consumed by the colimit -/

/-- The stage map attached to a bare family e, before S2024's datum is
assembled. -/
noncomputable def stageHomOfEquiv
    (e : forall U : Index p,
      CommGroup.torsion (Abelianization U) ≃* mu p U)
    (H : Index p) : Stage p H →+ ClosureTorsion p :=
  (additiveOfMulHom (muInGlobal p H)).comp
    (e H).toAdditive.toAddMonoidHom

/-- Compatibility of the stage maps with the transfer. -/
def StageCompat
    (e : forall U : Index p,
      CommGroup.torsion (Abelianization U) ≃* mu p U) : Prop :=
  forall {H K : Index p} (h : H <= K) (v : Stage p K),
    stageHomOfEquiv p e H (toStage p h v) = stageHomOfEquiv p e K v

/-- stageHomOfEquiv is S2024's stageHom when e comes from a datum. -/
theorem stageHomOfEquiv_eq_stageHom (data : LocalReciprocityData p) :
    stageHomOfEquiv p (fun U => data.equiv U) = stageHom p data :=
  rfl

/-- **The transfer square is equivalent to compatibility of the stage maps.**
S2024's stageHom_toStage is the forward direction; the converse is the
statement that the field is exactly what the universal property of muQZ
needs. -/
theorem transferCompat_iff_stage
    (e : forall U : Index p,
      CommGroup.torsion (Abelianization U) ≃* mu p U) :
    TransferCompat p e ↔ StageCompat p e := by
  constructor
  . intro hc H K h v
    have h := (transferCompat_iff_ambient p e).mp hc h (Additive.toMul v)
    simpa [stageHomOfEquiv, toStage] using congrArg Additive.ofMul h
  . intro hc
    apply (transferCompat_iff_ambient p e).mpr
    intro H K h v
    have h := hc h (Additive.ofMul v)
    simpa [stageHomOfEquiv, toStage] using congrArg Additive.toMul h

/-- The stage-map form for a completed datum, matching S2024's
stageHom_toStage. -/
theorem transferCompat_iff_stageHom (data : LocalReciprocityData p) :
    TransferCompat p (fun U => data.equiv U) ↔
      forall {H K : Index p} (h : H <= K) (v : Stage p K),
        stageHom p data H (toStage p h v) = stageHom p data K v := by
  simpa [StageCompat, stageHomOfEquiv_eq_stageHom] using
    transferCompat_iff_stage p (fun U => data.equiv U)

/-! ## 5. The inclusion side: reflexivity and composition -/

/-- The fixed-field inclusion for H = H is the identity. -/
theorem fixedFieldTorsionUnitsInclusion_refl (H : Index p) :
    fixedFieldTorsionUnitsInclusion p (le_refl H) = MonoidHom.id (mu p H) := by
  change RationalCircleCyclotome.torsionUnitsMap
      (IntermediateField.inclusion (fixedField_le p (le_refl H))).toRingHom =
    MonoidHom.id (mu p H)
  have h : fixedField_le p (le_refl H) = le_refl _ := Subsingleton.elim _ _
  rw [h, IntermediateField.inclusion_self]
  ext x
  rfl

/-- The fixed-field inclusions are compatible with composition:
incl_{K/L} o incl_{H/K} = incl_{H/L} for H <= K <= L. -/
theorem fixedFieldTorsionUnitsInclusion_comp {H K L : Index p}
    (hHK : H <= K) (hKL : K <= L) :
    (fixedFieldTorsionUnitsInclusion p hHK).comp
        (fixedFieldTorsionUnitsInclusion p hKL) =
      fixedFieldTorsionUnitsInclusion p (hHK.trans hKL) := by
  simp only [fixedFieldTorsionUnitsInclusion]
  rw [← torsionUnitsMap_comp]
  congr 1

/-! ## 6. The conditional reduction from S2027's source datum -/

/-- The local Artin family induced by S2027's source datum (M2a + M2c). -/
noncomputable def ofSourceData
    (d : S2027LocalArtinActual.LocalArtinSourceData p) :
    LocalArtinTorsionMap p where
  artin := fun U => (S2027LocalArtinActual.levelwiseEquiv p d U).symm

/-- The transfer square in the exact shape of S2027's htransfer hypothesis. -/
def SourceTransferCompat
    (d : S2027LocalArtinActual.LocalArtinSourceData p) : Prop :=
  forall {H K : Index p} (h : H <= K)
    (v : CommGroup.torsion (Abelianization K)),
    S2027LocalArtinActual.levelwiseEquiv p d H
        (torsionMap (verlagerungOpen p h) v) =
      fixedFieldTorsionUnitsInclusion p h
        (S2027LocalArtinActual.levelwiseEquiv p d K v)

/-- S2027's htransfer is exactly the source-level square for the induced
Artin family. -/
theorem artinTransferCompat_ofSource_iff
    (d : S2027LocalArtinActual.LocalArtinSourceData p) :
    ArtinTransferCompat p (ofSourceData p d) ↔ SourceTransferCompat p d := by
  simpa [SourceTransferCompat, TransferCompat, ofSourceData] using
    (transferCompat_iff_artin p (ofSourceData p d)).symm

/-- **Filling S2024's field from S2027's source datum and the square.** -/
noncomputable def localReciprocityDataOfSource
    (d : S2027LocalArtinActual.LocalArtinSourceData p)
    (hc : SourceTransferCompat p d) : LocalReciprocityData p :=
  localReciprocityDataOfArtin p (ofSourceData p d)
    ((artinTransferCompat_ofSource_iff p d).mpr hc)

/-- The levelwise equivalence of the constructed datum is S2027's
levelwiseEquiv. -/
theorem localReciprocityDataOfSource_equiv
    (d : S2027LocalArtinActual.LocalArtinSourceData p)
    (hc : SourceTransferCompat p d) :
    (localReciprocityDataOfSource p d hc).equiv =
      S2027LocalArtinActual.levelwiseEquiv p d := by
  funext U
  exact MulEquiv.symm_symm _

/-- S2027's source datum, together with the transfer square, gives S2024's
missing datum. -/
theorem localReciprocityDataMissing_of_source
    (h : exists d : S2027LocalArtinActual.LocalArtinSourceData p,
      SourceTransferCompat p d) :
    localReciprocityDataMissing p := by
  obtain ⟨d, hd⟩ := h
  exact ⟨localReciprocityDataOfSource p d hd⟩

/-- S2027's source datum already supplies the first missing input (M2a). -/
theorem localArtinTorsionMissing_of_sourceData
    (h : Nonempty (S2027LocalArtinActual.LocalArtinSourceData p)) :
    localArtinTorsionMissing p := by
  obtain ⟨d⟩ := h
  exact ⟨ofSourceData p d⟩

/-! ## 7. Axiom probes -/

#print axioms transferCompat_iff_artin
#print axioms localReciprocityDataOfArtin
#print axioms artinTransferCompat_of_data
#print axioms localReciprocityDataMissing_iff_artinSource
#print axioms localArtinTorsionMissing_of_dataMissing
#print axioms transferCompat_iff_ambient
#print axioms transferCompat_iff_stage
#print axioms transferCompat_iff_stageHom
#print axioms fixedFieldTorsionUnitsInclusion_refl
#print axioms fixedFieldTorsionUnitsInclusion_comp
#print axioms artinTransferCompat_ofSource_iff
#print axioms localReciprocityDataOfSource
#print axioms localReciprocityDataMissing_of_source
#print axioms localArtinTorsionMissing_of_sourceData

end LeanFormal.IUT.XiFPaper.S2048TransferCompatActual
