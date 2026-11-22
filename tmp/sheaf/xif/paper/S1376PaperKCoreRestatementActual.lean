/-
# S1376: paper-faithful K-core restatement of the geometric core and clause (d)

Paper anchor: IUT I, Definition 3.1(d) (corpus lines 3185-3215): the K-core is
the base change C_K = C_F x_F K of the F-side quotient, and X_K -> C_K is the
natural finite-etale cover.  In particular X_K is *not* the scalar extension
X_F x_F K; the l-torsion decoration of X_K is additional K-side structure.

S1360's genus-only repair made the D5-D9 records logically consistent, but the
geometric core still carried

  xKExtension : SourceOrbicurveScalarExtension A.F A.K xF
  xK_eq_extension : xK = xKExtension.result

and clause (d) still carried the corresponding scalar-extension quotient
fields

  k_quotientExtension : SourceOrbicurveMorphismScalarExtension
    S.xKExtension S.cKExtension S.quotient.map
  k_quotient_map_eq_extension : k_quotient.map = Hom.cast ... k_quotientExtension.result

This file restates the *actual* (A = S1280Arithmetic l) geometric core and
clause (d) with the paper's K-side, using the S1360 structures directly:

* `S1360KCoreBaseChange`: C_K = C_F x_F K;
* `S1360KCoreIdentification`: X_K of type (1,l-tors), the finite-etale cover
  X_K -> C_K, and C_K of type (1,l-tors)^+-.

The restated core contains no `xKExtension`/`xK_eq_extension` field.  The
restated clause (d) contains no `k_quotientExtension`/`k_quotient_map_eq_extension`
field; instead `k_quotient_map_eq_kCore_cover` says that the K-side quotient
map *is* the K-core finite-etale cover.

The restatement is not terminal, empty or fake:

* an old geometric core together with its actual finite-etale cover gives a
  restated core (`S1376PaperCore.ofGeometricCore`);
* every old clause (d) record gives a restated clause (d) record, using its
  actual `k_l_torsion_cover` as the K-core cover
  (`S1376PaperClauseD.ofSourceClauseD`);
* the reverse direction takes exactly the two removed scalar-extension fields
  as explicit hypotheses (`S1376PaperClauseD.toSourceClauseD`), so no extra
  geometric data is invented;
* the exact first field is the actual `S.xK`, and with nonterminality it is
  the first field of the S1360 D9 orbicurve slot; terminal constant stacks and
  point fibers are excluded.

The base-change component is exposed separately as `S1360KCoreBaseChange` via
`S1376PaperCore.kCoreBase` and `S1376PaperClauseD.kCoreBase`.  The
place/selected-place fields of `SourceSignQuotientData` are orthogonal to the
K-side and are not restated here; this file restates the geometric core and
clause (d) only.

No inhabitant of a geometric record is constructed from nothing.
-/

import tmp.sheaf.xif.paper.S1360D9OrbicurveSlotActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1376PaperKCoreRestatementActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1360D9OrbicurveSlotActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

/-! ## 1. Transporting the K-core cover to the actual C_K -/

/-- Transporting an orbicurve morphism along equalities preserves
representable finite-etale-ness.  This is the only transport used below; it
lets the K-core cover `X_K -> C_K` be compared with the quotient map at the
actual `C_K` of the record. -/
noncomputable def s1376HomCast_finiteEtale
    {F : Type u} [Field F]
    {X X' Y Y' : Iut.HyperbolicOrbicurve F}
    (hX : X = X') (hY : Y = Y') (f : X.Hom Y)
    (hf : Iut.EtaleStackFiniteEtaleMorphism f) :
    Iut.EtaleStackFiniteEtaleMorphism
      (Iut.HyperbolicOrbicurve.Hom.cast hX hY f) := by
  subst hX
  subst hY
  exact hf

/-- The K-core finite-etale cover `X -> C_K`, transported to the actual
`C_K` of a consumer record.  The source and target are fixed in the type, as
in `SourceOrbicurveFiniteEtaleCover`. -/
noncomputable def s1376KCoreCoverAt
    {l : PrimeGeFive}
    {X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K}
    (K : S1360KCoreIdentification l X)
    (cK : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hcK : K.cK = cK) :
    SourceOrbicurveFiniteEtaleCover X cK where
  map := Iut.HyperbolicOrbicurve.Hom.cast rfl hcK K.coverMap
  finiteEtale :=
    s1376HomCast_finiteEtale rfl hcK K.coverMap K.coverFiniteEtale

/-- The exact first field carried by a K-core identification: the actual
`X_K`, with its paper `(1,l-tors)` signature.  No scalar extension of `X_F`
appears. -/
def s1376KCoreFirstField
    {l : PrimeGeFive}
    {X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K}
    (K : S1360KCoreIdentification l X) :
    S1360PaperOrbicurveFirstField l :=
  ⟨X, K.x_type⟩

@[simp] theorem s1376KCoreFirstField_val
    {l : PrimeGeFive}
    {X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K}
    (K : S1360KCoreIdentification l X) :
    (s1376KCoreFirstField K :
      Iut.HyperbolicOrbicurve (S1280Arithmetic l).K) = X :=
  rfl

/-- The K-core base change is for `C_K`, not for `X_K`. -/
theorem s1376KCore_cK_eq_baseChange
    {l : PrimeGeFive}
    {X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K}
    (K : S1360KCoreIdentification l X) :
    K.cK = K.cKExtension.result :=
  K.cK_eq_extension

/-- The K-core finite-etale cover really is a finite-etale morphism. -/
noncomputable def s1376KCore_coverMap_finiteEtale
    {l : PrimeGeFive}
    {X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K}
    (K : S1360KCoreIdentification l X) :
    Iut.EtaleStackFiniteEtaleMorphism K.coverMap :=
  K.coverFiniteEtale

/-! ## 2. Paper-faithful geometric core -/

/-- The paper-faithful restatement of (the actual instance of)
`SourceSignQuotientGeometricCore`.

The F-side fields are exactly those of the geometric core.  The F-side
quotient `C_F` is read from the K-core base change, and the K-side is a single
`S1360KCoreIdentification`:

* `C_K = C_F x_F K`;
* `X_K` has type `(1,l-tors)` and `C_K` has type `(1,l-tors)^+-`;
* there is a finite-etale cover `X_K -> C_K`.

There is deliberately no `xKExtension : SourceOrbicurveScalarExtension A.F A.K xF`
and no `xK = xKExtension.result`. -/
structure S1376PaperCore (l : PrimeGeFive) where
  /-- F-side once-punctured elliptic curve. -/
  xF : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F
  xF_geometry : SourceOncePuncturedGeometry (S1280Arithmetic l).curve xF
  ellipticInvolution : xF.Hom xF
  ellipticInvolution_squared :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp ellipticInvolution ellipticInvolution)
      (Iut.HyperbolicOrbicurve.Hom.id xF)
  unique_elliptic_involution :
    ∀ inv : xF.Hom xF,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id xF) →
      inv = ellipticInvolution
  signAction : Iut.OrbicurveSignAction xF
  signAction_inversion_eq_ellipticInvolution :
    signAction.inversion = ellipticInvolution
  /-- K-side orbicurve `X_K`, of paper type `(1,l-tors)`. -/
  xK : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K
  /-- The K-core: `C_K = C_F x_F K` plus the finite-etale cover
  `X_K -> C_K`. -/
  kCore : S1360KCoreIdentification l xK
  /-- The sign quotient is `X_F -> C_F`; `C_F` is the F-side object of the
  K-core base change, so no second `C_F` is introduced. -/
  quotient : Iut.OrbicurveSignInvariantMorphism signAction kCore.cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient
  xFGroups :
    SourceOrbicurveGroupData xF (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).F)
  cFGroups :
    SourceOrbicurveGroupData kCore.cF
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).F)
  fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
    xFGroups.sequence.geometric xFGroups.sequence.arithmetic
    cFGroups.sequence.geometric cFGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).F)
    xFGroups.sequence cFGroups.sequence
  /-- Boundary cusp of `C_K`. -/
  epsilon : Iut.OrbicurveBoundaryCusp kCore.cK

namespace S1376PaperCore

variable {l : PrimeGeFive}
variable (P : S1376PaperCore l)

/-- The F-side quotient `C_F`, read from the K-core base change. -/
abbrev cF : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F :=
  P.kCore.cF

/-- The K-side quotient `C_K`. -/
abbrev cK : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K :=
  P.kCore.cK

/-- The K-core scalar extension `C_K = C_F x_F K`. -/
abbrev cKExtension :
    SourceOrbicurveScalarExtension (S1280Arithmetic l).F
      (S1280Arithmetic l).K P.cF :=
  P.kCore.cKExtension

/-- The K-core base change, as a theorem about the actual `C_K`/`C_F`. -/
theorem cK_eq_baseChange : P.cK = P.cKExtension.result :=
  P.kCore.cK_eq_extension

/-- The base-change component of the paper core, exposed as the
`S1360KCoreBaseChange` that the identification extends. -/
def kCoreBase (P : S1376PaperCore l) : S1360KCoreBaseChange l where
  cF := P.kCore.cF
  cK := P.kCore.cK
  cKExtension := P.kCore.cKExtension
  cK_eq_extension := P.kCore.cK_eq_extension
  cK_type := P.kCore.cK_type

/-- The exposed base change is exactly the K-core base change: it is a base
change of `C_K`, not a scalar extension of `X_K`. -/
theorem kCoreBase_cK_eq_extension (P : S1376PaperCore l) :
    (kCoreBase P).cK = (kCoreBase P).cKExtension.result :=
  (kCoreBase P).cK_eq_extension

theorem xF_type : P.xF.signature = sourceTypeOneOne :=
  P.xF_geometry.signature

theorem xK_type : P.xK.signature = sourceTypeOneLTorsion l :=
  P.kCore.x_type

theorem cK_type : P.cK.signature = sourceTypeOneLTorsionPlusMinus l :=
  P.kCore.cK_type

noncomputable def coverMap_finiteEtale :
    Iut.EtaleStackFiniteEtaleMorphism P.kCore.coverMap :=
  P.kCore.coverFiniteEtale

theorem cK_genus_eq_cF_genus :
    P.cK.signature.genus = P.cF.signature.genus := by
  calc
    P.cK.signature.genus = P.cKExtension.result.signature.genus := by
      rw [P.cK_eq_baseChange]
    _ = P.cF.signature.genus := P.cKExtension.genus_preserved

/-- The F-side quotient has genus one, as forced by the K-core base change and
the `(1,l-tors)^+-` type of `C_K`. -/
theorem cF_genus_one : P.cF.signature.genus = 1 := by
  calc
    P.cF.signature.genus = P.cKExtension.result.signature.genus :=
      P.cKExtension.genus_preserved.symm
    _ = P.cK.signature.genus := by rw [P.cK_eq_baseChange]
    _ = 1 := by
      rw [P.cK_type]
      rfl

theorem xK_genus_one : P.xK.signature.genus = 1 := by
  rw [P.xK_type]
  rfl

/-- The paper F-side and K-side types are distinct: `(1,1)` has one puncture,
`(1,l-tors)` has none.  This is the same consistency as S1360/S1370, now with
the K-side carried by the K-core identification. -/
theorem xK_signature_ne_xF : P.xK.signature ≠ P.xF.signature := by
  intro h
  have hF' : P.xF.signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic := by
    rw [P.xF_type]
    apply Iut.OrbicurveSignature.ext <;> rfl
  exact s1360OncePunctured_ne_sourceTypeOneLTorsion l
    (P.xK_type.symm.trans (h.trans hF')).symm

/-- The whole paper K-side in one Prop-valued statement: the base change is
for C_K and the two K-side types are the paper types.  The finite-etale
certificate is `coverMap_finiteEtale`; it is data, not a proposition. -/
theorem kSide_spec :
    P.cK = P.cKExtension.result ∧
    P.xK.signature = sourceTypeOneLTorsion l ∧
    P.cK.signature = sourceTypeOneLTorsionPlusMinus l :=
  ⟨P.cK_eq_baseChange, P.xK_type, P.cK_type⟩

/-! ### Non-vacuity: an old core plus its actual cover gives a paper core -/

/-- A paper core built from an old geometric core and an actual finite-etale
cover `X_K -> C_K`.  The two obsolete scalar-extension fields
`xKExtension`/`xK_eq_extension` of the old core are not used. -/
noncomputable def ofGeometricCore
    (G : SourceSignQuotientGeometricCore (S1280Arithmetic l))
    (cover : SourceOrbicurveFiniteEtaleCover G.xK G.cK) :
    S1376PaperCore l where
  xF := G.xF
  xF_geometry := G.xF_geometry
  ellipticInvolution := G.ellipticInvolution
  ellipticInvolution_squared := G.ellipticInvolution_squared
  unique_elliptic_involution := G.unique_elliptic_involution
  signAction := G.signAction
  signAction_inversion_eq_ellipticInvolution :=
    G.signAction_inversion_eq_ellipticInvolution
  xK := G.xK
  kCore :=
    { cF := G.cF
      cK := G.cK
      cKExtension := G.cKExtension
      cK_eq_extension := G.cK_eq_extension
      cK_type := G.cKType
      x_type := G.xKType
      coverMap := cover.map
      coverFiniteEtale := cover.finiteEtale }
  quotient := G.quotient
  quotientWitness := G.quotientWitness
  xFGroups := G.xFGroups
  cFGroups := G.cFGroups
  fGroupInclusion := G.fGroupInclusion
  epsilon := G.epsilon

@[simp] theorem ofGeometricCore_xF
    (G : SourceSignQuotientGeometricCore (S1280Arithmetic l))
    (cover : SourceOrbicurveFiniteEtaleCover G.xK G.cK) :
    (ofGeometricCore G cover).xF = G.xF :=
  rfl

@[simp] theorem ofGeometricCore_xK
    (G : SourceSignQuotientGeometricCore (S1280Arithmetic l))
    (cover : SourceOrbicurveFiniteEtaleCover G.xK G.cK) :
    (ofGeometricCore G cover).xK = G.xK :=
  rfl

@[simp] theorem ofGeometricCore_cF
    (G : SourceSignQuotientGeometricCore (S1280Arithmetic l))
    (cover : SourceOrbicurveFiniteEtaleCover G.xK G.cK) :
    (ofGeometricCore G cover).cF = G.cF :=
  rfl

@[simp] theorem ofGeometricCore_cK
    (G : SourceSignQuotientGeometricCore (S1280Arithmetic l))
    (cover : SourceOrbicurveFiniteEtaleCover G.xK G.cK) :
    (ofGeometricCore G cover).cK = G.cK :=
  rfl

@[simp] theorem ofGeometricCore_coverMap
    (G : SourceSignQuotientGeometricCore (S1280Arithmetic l))
    (cover : SourceOrbicurveFiniteEtaleCover G.xK G.cK) :
    (ofGeometricCore G cover).kCore.coverMap = cover.map :=
  rfl

end S1376PaperCore

/-! ## 3. Paper-faithful clause (d) -/

/-- The paper-faithful restatement of the actual instance of `SourceClauseD`.

The K-side data are the K-core identification of Definition 3.1(d):
`C_K = C_F x_F K`, the finite-etale cover `X_K -> C_K`, and the fundamental
group data.  The quotient map is identified with the K-core cover; the
scalar-extension quotient fields `k_quotientExtension` and
`k_quotient_map_eq_extension` are absent. -/
structure S1376PaperClauseD
    {l : PrimeGeFive}
    (S : SourceSignQuotientData (S1280Arithmetic l))
    (C : SourceClauseA (S1280Arithmetic l) S)
    (B : SourceClauseB (S1280Arithmetic l) S C)
    (D : SourceClauseC (S1280Arithmetic l) S C B) where
  /-- The K-core base change and identification, at the actual `X_K`. -/
  kCore : S1360KCoreIdentification l S.xK
  /-- The K-core's `C_F` is the actual F-side `C_F` of the record. -/
  kCore_cF : kCore.cF = S.cF
  /-- The K-core's `C_K` is the actual K-side `C_K` of the record. -/
  kCore_cK : kCore.cK = S.cK
  k_signAction : Iut.OrbicurveSignAction S.xK
  k_quotient : Iut.OrbicurveSignInvariantMorphism k_signAction S.cK
  k_quotientWitness :
    Iut.OrbicurveSignQuotientWitness k_signAction k_quotient
  /-- The K-side quotient map is the K-core finite-etale cover.  This replaces
  `k_quotientExtension`/`k_quotient_map_eq_extension`. -/
  k_quotient_map_eq_kCore_cover :
    k_quotient.map = Iut.HyperbolicOrbicurve.Hom.cast rfl kCore_cK kCore.coverMap
  x_groups :
    SourceOrbicurveGroupData S.xK
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)
  c_groups :
    SourceOrbicurveGroupData S.cK
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)
  group_inclusion :
    Iut.ProfiniteFundamentalGroupInclusion
      x_groups.sequence.geometric x_groups.sequence.arithmetic
      c_groups.sequence.geometric c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)
      x_groups.sequence c_groups.sequence
  x_to_F_groups :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      x_groups.sequence.geometric x_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)
      S.xFGroups.sequence.geometric S.xFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).F)
      x_groups.sequence S.xFGroups.sequence
  c_to_F_groups :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      c_groups.sequence.geometric c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)
      S.cFGroups.sequence.geometric S.cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).F)
      c_groups.sequence S.cFGroups.sequence

namespace S1376PaperClauseD

variable {l : PrimeGeFive}
variable {S : SourceSignQuotientData (S1280Arithmetic l)}
variable {C : SourceClauseA (S1280Arithmetic l) S}
variable {B : SourceClauseB (S1280Arithmetic l) S C}
variable {D : SourceClauseC (S1280Arithmetic l) S C B}
variable (P : S1376PaperClauseD S C B D)

/-- The K-core cover transported to the record's actual `C_K`. -/
noncomputable def cover (P : S1376PaperClauseD S C B D) :
    SourceOrbicurveFiniteEtaleCover S.xK S.cK :=
  s1376KCoreCoverAt P.kCore S.cK P.kCore_cK

/-- The K-core base change at the actual `C_K` of the record. -/
theorem cK_eq_baseChange (P : S1376PaperClauseD S C B D) :
    S.cK = P.kCore.cKExtension.result :=
  P.kCore_cK.symm.trans P.kCore.cK_eq_extension

/-- The base-change component of the paper clause (d), exposed as the
`S1360KCoreBaseChange` that the identification extends. -/
def kCoreBase (P : S1376PaperClauseD S C B D) : S1360KCoreBaseChange l where
  cF := P.kCore.cF
  cK := P.kCore.cK
  cKExtension := P.kCore.cKExtension
  cK_eq_extension := P.kCore.cK_eq_extension
  cK_type := P.kCore.cK_type

/-- The exposed base change is the K-core base change of `C_K`. -/
theorem kCoreBase_cK_eq_extension (P : S1376PaperClauseD S C B D) :
    (kCoreBase P).cK = (kCoreBase P).cKExtension.result :=
  (kCoreBase P).cK_eq_extension

/-- The K-core base change uses the record's actual `C_F`. -/
theorem kCoreBase_cF_eq (P : S1376PaperClauseD S C B D) :
    (kCoreBase P).cF = S.cF :=
  P.kCore_cF

/-- The K-core base change uses the record's actual `C_K`. -/
theorem kCoreBase_cK_eq (P : S1376PaperClauseD S C B D) :
    (kCoreBase P).cK = S.cK :=
  P.kCore_cK

/-- The K-core's `C_F` is the record's `C_F`. -/
theorem cF_eq (P : S1376PaperClauseD S C B D) : P.kCore.cF = S.cF :=
  P.kCore_cF

theorem xK_type (P : S1376PaperClauseD S C B D) :
    S.xK.signature = sourceTypeOneLTorsion l :=
  P.kCore.x_type

theorem cK_type (P : S1376PaperClauseD S C B D) :
    S.cK.signature = sourceTypeOneLTorsionPlusMinus l := by
  rw [← P.kCore_cK]
  exact P.kCore.cK_type

/-- The K-side quotient map is finite etale, because it *is* the K-core
finite-etale cover. -/
noncomputable def kQuotient_finiteEtale :
    Iut.EtaleStackFiniteEtaleMorphism P.k_quotient.map := by
  rw [P.k_quotient_map_eq_kCore_cover]
  exact s1376HomCast_finiteEtale rfl P.kCore_cK P.kCore.coverMap
    P.kCore.coverFiniteEtale

/-- The cover field in the old clause-(d) shape is recovered from the K-core;
its map is the quotient map.  This is the replacement for the old
`k_l_torsion_cover`/`k_l_torsion_cover_map_eq_quotient` pair. -/
theorem cover_map_eq_quotient : (cover P).map = P.k_quotient.map :=
  P.k_quotient_map_eq_kCore_cover.symm

/-- The F-side quotient has genus one. -/
theorem cF_genus_one (P : S1376PaperClauseD S C B D) :
    S.cF.signature.genus = 1 := by
  calc
    S.cF.signature.genus = P.kCore.cF.signature.genus := by
      rw [P.kCore_cF]
    _ = P.kCore.cKExtension.result.signature.genus :=
      P.kCore.cKExtension.genus_preserved.symm
    _ = P.kCore.cK.signature.genus := by
      rw [P.kCore.cK_eq_extension]
    _ = 1 := by
      rw [P.kCore.cK_type]
      rfl

theorem xK_genus_one (P : S1376PaperClauseD S C B D) :
    S.xK.signature.genus = 1 := by
  rw [P.xK_type]
  rfl

/-- The paper K-side of clause (d) in one Prop-valued statement.  The
finite-etale certificate is `kQuotient_finiteEtale`; it is data, not a
proposition. -/
theorem kSide_spec (P : S1376PaperClauseD S C B D) :
    S.cK = P.kCore.cKExtension.result ∧
    P.kCore.cF = S.cF ∧
    S.xK.signature = sourceTypeOneLTorsion l ∧
    S.cK.signature = sourceTypeOneLTorsionPlusMinus l :=
  ⟨P.cK_eq_baseChange, P.cF_eq, P.xK_type, P.cK_type⟩

/-! ### Exact first field -/

/-- The exact first field of the paper clause (d): the actual `X_K` with its
paper `(1,l-tors)` signature.  This is the D9 first-field type, not a scalar
extension of `X_F`. -/
def firstField : S1360PaperOrbicurveFirstField l :=
  ⟨S.xK, P.xK_type⟩

/-- The exact first field in the base orbicurve type, definitionally the
D9 first field `S.xK`. -/
abbrev exactFirstField (P : S1376PaperClauseD S C B D) :
    S1360OrbicurveFirstField l :=
  S.xK

/-- The exact first field and the paper-typed first field have the same
underlying orbicurve. -/
@[simp] theorem exactFirstField_eq_firstField_val
    (P : S1376PaperClauseD S C B D) :
    P.exactFirstField =
      (P.firstField : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K) :=
  rfl

@[simp] theorem firstField_val :
    (P.firstField : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K) = S.xK :=
  rfl

theorem firstField_signature :
    (P.firstField : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K).signature =
      sourceTypeOneLTorsion l :=
  P.xK_type

/-- With the actual nonterminality certificate, the restated clause (d) gives
the S1360 D9 orbicurve slot; its first field is exactly `P.firstField`. -/
noncomputable def toD9Slot
    (h : S1319NonterminalFiber S.xK) :
    S1360D9OrbicurveSlot l where
  orbicurve :=
    { X := S.xK
      nonterminal := h
      signature := P.xK_type
      groups := P.x_groups.groups }
  kCore := P.kCore

@[simp] theorem toD9Slot_firstField
    (h : S1319NonterminalFiber S.xK) :
    (P.toD9Slot h).firstField = S.xK :=
  rfl

/-- The D9 slot first field is exactly the subtype first field of the paper
clause (d). -/
@[simp] theorem toD9Slot_firstField_eq_firstField
    (h : S1319NonterminalFiber S.xK) :
    (P.toD9Slot h).firstField =
      (P.firstField : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K) :=
  rfl

theorem toD9Slot_signature
    (h : S1319NonterminalFiber S.xK) :
    (P.toD9Slot h).firstField.signature = sourceTypeOneLTorsion l :=
  (P.toD9Slot h).signature

/-- The exact first field is not the terminal constant stack.  This holds
without any nonterminality hypothesis: no hyperbolic orbicurve at all is
carried by the terminal constant stack. -/
theorem firstField_not_terminal (P : S1376PaperClauseD S C B D) :
    S.xK.stack ≠
      Definition31OrbicurveInstance.terminalConstantEtaleStack
        (S1280Arithmetic l).K :=
  Definition31OrbicurveInstance.terminalConstantEtaleStack_not_hyperbolicOrbicurve_carrier
    (S1280Arithmetic l).K S.xK

/-- The exact first field is not a point fiber (given the actual
nonterminality certificate). -/
theorem firstField_not_pointFiber (P : S1376PaperClauseD S C B D)
    (h : S1319NonterminalFiber S.xK) :
    ¬ IsPointFiber S.xK.stack.fiber := by
  intro hp
  exact s1360PointFiber_not_nonterminal hp h

/-! ### Exact relation to the old clause (d) -/

/-- Every old actual clause (d) record gives a paper clause (d) record.  The
construction uses only the actual `k_l_torsion_cover` as the K-core cover and
never touches the obsolete scalar-extension fields. -/
noncomputable def ofSourceClauseD
    (E : SourceClauseD (S1280Arithmetic l) S C B D) :
    S1376PaperClauseD S C B D where
  kCore :=
    { cF := S.cF
      cK := S.cK
      cKExtension := S.cKExtension
      cK_eq_extension := S.cK_eq_extension
      cK_type := S.cKType
      x_type := S.xKType
      coverMap := E.k_l_torsion_cover.map
      coverFiniteEtale := E.k_l_torsion_cover.finiteEtale }
  kCore_cF := rfl
  kCore_cK := rfl
  k_signAction := E.k_signAction
  k_quotient := E.k_quotient
  k_quotientWitness := E.k_quotientWitness
  k_quotient_map_eq_kCore_cover :=
    E.k_l_torsion_cover_map_eq_quotient.symm
  x_groups := E.x_groups
  c_groups := E.c_groups
  group_inclusion := E.group_inclusion
  x_to_F_groups := E.x_to_F_groups
  c_to_F_groups := E.c_to_F_groups

@[simp] theorem ofSourceClauseD_kCore_coverMap
    (E : SourceClauseD (S1280Arithmetic l) S C B D) :
    (ofSourceClauseD (S := S) (C := C) (B := B) (D := D) E).kCore.coverMap =
      E.k_l_torsion_cover.map :=
  rfl

@[simp] theorem ofSourceClauseD_kCore_cF
    (E : SourceClauseD (S1280Arithmetic l) S C B D) :
    (ofSourceClauseD (S := S) (C := C) (B := B) (D := D) E).kCore.cF =
      S.cF :=
  rfl

@[simp] theorem ofSourceClauseD_kCore_cK
    (E : SourceClauseD (S1280Arithmetic l) S C B D) :
    (ofSourceClauseD (S := S) (C := C) (B := B) (D := D) E).kCore.cK =
      S.cK :=
  rfl

/-- The reverse direction: a paper clause (d) record plus exactly the two old
scalar-extension quotient fields reconstructs an old clause (d) record.  Thus
the restatement removes exactly `k_quotientExtension` and
`k_quotient_map_eq_extension`; no other clause-(d) data is lost. -/
noncomputable def toSourceClauseD
    (kQuotientExtension : SourceOrbicurveMorphismScalarExtension
      S.xKExtension S.cKExtension S.quotient.map)
    (kQuotientMapEqExtension :
      P.k_quotient.map = Iut.HyperbolicOrbicurve.Hom.cast
        S.xK_eq_extension.symm S.cK_eq_extension.symm
        kQuotientExtension.result) :
    SourceClauseD (S1280Arithmetic l) S C B D where
  k_signAction := P.k_signAction
  k_quotient := P.k_quotient
  k_quotientWitness := P.k_quotientWitness
  k_quotientExtension := kQuotientExtension
  k_quotient_map_eq_extension := kQuotientMapEqExtension
  k_l_torsion_cover := cover P
  k_l_torsion_cover_map_eq_quotient := cover_map_eq_quotient P
  x_groups := P.x_groups
  c_groups := P.c_groups
  group_inclusion := P.group_inclusion
  x_to_F_groups := P.x_to_F_groups
  c_to_F_groups := P.c_to_F_groups

/-- Reconstructing the old record and then restating returns the original old
record. -/
@[simp] theorem toSourceClauseD_ofSourceClauseD
    (E : SourceClauseD (S1280Arithmetic l) S C B D) :
    toSourceClauseD
      (ofSourceClauseD (S := S) (C := C) (B := B) (D := D) E)
      E.k_quotientExtension E.k_quotient_map_eq_extension = E := by
  cases E
  rfl

end S1376PaperClauseD

/-! ## 4. Axiom footprint -/

#print axioms s1376HomCast_finiteEtale
#print axioms s1376KCoreCoverAt
#print axioms s1376KCoreFirstField
#print axioms s1376KCore_cK_eq_baseChange
#print axioms s1376KCore_coverMap_finiteEtale
#print axioms S1376PaperCore.ofGeometricCore
#print axioms S1376PaperCore.cK_eq_baseChange
#print axioms S1376PaperCore.kCoreBase
#print axioms S1376PaperCore.kCoreBase_cK_eq_extension
#print axioms S1376PaperCore.cK_genus_eq_cF_genus
#print axioms S1376PaperCore.cF_genus_one
#print axioms S1376PaperCore.xK_genus_one
#print axioms S1376PaperCore.xK_signature_ne_xF
#print axioms S1376PaperCore.kSide_spec
#print axioms S1376PaperClauseD.cover
#print axioms S1376PaperClauseD.cK_eq_baseChange
#print axioms S1376PaperClauseD.kCoreBase
#print axioms S1376PaperClauseD.kCoreBase_cK_eq_extension
#print axioms S1376PaperClauseD.cF_eq
#print axioms S1376PaperClauseD.xK_type
#print axioms S1376PaperClauseD.cK_type
#print axioms S1376PaperClauseD.kQuotient_finiteEtale
#print axioms S1376PaperClauseD.cover_map_eq_quotient
#print axioms S1376PaperClauseD.cF_genus_one
#print axioms S1376PaperClauseD.xK_genus_one
#print axioms S1376PaperClauseD.kSide_spec
#print axioms S1376PaperClauseD.firstField
#print axioms S1376PaperClauseD.firstField_val
#print axioms S1376PaperClauseD.exactFirstField
#print axioms S1376PaperClauseD.exactFirstField_eq_firstField_val
#print axioms S1376PaperClauseD.toD9Slot
#print axioms S1376PaperClauseD.toD9Slot_firstField
#print axioms S1376PaperClauseD.toD9Slot_firstField_eq_firstField
#print axioms S1376PaperClauseD.toD9Slot_signature
#print axioms S1376PaperClauseD.firstField_not_terminal
#print axioms S1376PaperClauseD.firstField_not_pointFiber
#print axioms S1376PaperClauseD.ofSourceClauseD
#print axioms S1376PaperClauseD.toSourceClauseD
#print axioms S1376PaperClauseD.toSourceClauseD_ofSourceClauseD

end LeanFormal.IUT.XiFPaper.S1376PaperKCoreRestatementActual

end
