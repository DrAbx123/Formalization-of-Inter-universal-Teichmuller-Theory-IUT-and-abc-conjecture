import tmp.sheaf.xif.paper.S1881D9D7bActual
import tmp.sheaf.xif.paper.S1360D9OrbicurveSlotActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

/-!
# S1984: audit of the K-side objects xK, cK, cF, coverMap

This file is an audit companion to
coord/reports/S1984KSideObjectAudit.md.  It does not edit any production
definition and does not assert any missing geometric construction.

The declarations below record, in Lean, the exact object equations and the
label/role conflicts of the K-side contracts:

* production: SourceSignQuotientData and SourceClauseD;
* paper target: S1881D9OrbicurveSlot and S1360KCoreIdentification.

The last part defines the paper-faithful K-side interface and isolates the
precise missing cover data.  No inhabitant of the missing cover data is
asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1984KSideObjectAudit

universe u

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1360D9OrbicurveSlotActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual

/-! ## 1. Label arithmetic: cores and l-tors covers are different types -/

/-- (1,1) (the core X_F/X_K) is not the (1,l-tors) label: the latter
has no punctures and an order-l stacky point. -/
theorem sourceTypeOneOne_ne_sourceTypeOneLTorsion (l : PrimeGeFive) :
    sourceTypeOneOne ≠ sourceTypeOneLTorsion l := by
  intro h
  have hp : sourceTypeOneOne.punctures =
      (sourceTypeOneLTorsion l).punctures :=
    congrArg Iut.OrbicurveSignature.punctures h
  simp [sourceTypeOneOne, sourceTypeOneLTorsion] at hp

/-- (1,1)^± (the core C_F/C_K) is not (1,l-tors)^±: at the label
level the latter has two stacky orders.  This is the role distinction used
below, independent of the later honest-value correction. -/
theorem sourceTypeOneOnePlusMinus_ne_sourceTypeOneLTorsionPlusMinus
    (l : PrimeGeFive) :
    sourceTypeOneOnePlusMinus ≠ sourceTypeOneLTorsionPlusMinus l := by
  intro h
  have hlen : sourceTypeOneOnePlusMinus.stackyOrders.length =
      (sourceTypeOneLTorsionPlusMinus l).stackyOrders.length :=
    congrArg (fun s : Iut.OrbicurveSignature => s.stackyOrders.length) h
  simp [sourceTypeOneOnePlusMinus, sourceTypeOneLTorsionPlusMinus] at hlen

/-- The (1,1) label is also different from (1,l-tors)^±. -/
theorem sourceTypeOneOne_ne_sourceTypeOneLTorsionPlusMinus
    (l : PrimeGeFive) :
    sourceTypeOneOne ≠ sourceTypeOneLTorsionPlusMinus l := by
  intro h
  have hp : sourceTypeOneOne.punctures =
      (sourceTypeOneLTorsionPlusMinus l).punctures :=
    congrArg Iut.OrbicurveSignature.punctures h
  simp [sourceTypeOneOne, sourceTypeOneLTorsionPlusMinus] at hp

/-! ## 2. Production: xK and cK are the K-cores -/

theorem sourceSignQuotient_xK_is_core
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.xK = S.xKExtension.result :=
  S.xK_eq_extension

theorem sourceSignQuotient_cK_is_core
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.cK = S.cKExtension.result :=
  S.cK_eq_extension

/-- The production contract labels the core xK by the (1,l-tors) cover
type. -/
theorem sourceSignQuotient_xK_label
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.xK.signature = sourceTypeOneLTorsion l :=
  S.xKType

/-- The production contract labels the core cK by the (1,l-tors)^± cover
type. -/
theorem sourceSignQuotient_cK_label
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.cK.signature = sourceTypeOneLTorsionPlusMinus l :=
  S.cKType

/-- Consequently the core xK cannot simultaneously carry the paper core
label (1,1). -/
theorem sourceSignQuotient_xK_not_core_label
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.xK.signature ≠ sourceTypeOneOne := by
  rw [S.xKType]
  exact (sourceTypeOneOne_ne_sourceTypeOneLTorsion l).symm

/-- The core cK cannot carry the (1,1) label either. -/
theorem sourceSignQuotient_cK_not_XK_core_label
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.cK.signature ≠ sourceTypeOneOne := by
  rw [S.cKType]
  exact (sourceTypeOneOne_ne_sourceTypeOneLTorsionPlusMinus l).symm

/-- Consequently the core cK cannot simultaneously carry the paper core
label (1,1)^±. -/
theorem sourceSignQuotient_cK_not_core_label
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.cK.signature ≠ sourceTypeOneOnePlusMinus := by
  rw [S.cKType]
  exact (sourceTypeOneOnePlusMinus_ne_sourceTypeOneLTorsionPlusMinus l).symm

/-- cF is the codomain of the actual sign quotient, so it is an object of
the sign-quotient package; the package stores no cF signature. -/
theorem sourceSignQuotient_cF_is_quotient_codomain
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    (S.quotient.map : S.xF.Hom S.cF) = S.quotient.map :=
  rfl

/-- The only cF genus statement in the production package is the one forced
by the mislabelled cK: it says genus one. -/
theorem sourceSignQuotient_cF_genus_one
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.cF.signature.genus = 1 :=
  S.cF_genus

/-! ## 3. Production clause (d): the l-torsion cover is the core quotient -/

/-- In SourceClauseD, the field named k_l_torsion_cover is literally the
sign-quotient map k_quotient. -/
theorem sourceClauseD_lTorsionCover_eq_quotient
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    E.k_l_torsion_cover.map = E.k_quotient.map :=
  E.k_l_torsion_cover_map_eq_quotient

/-- The same map, with the source and target fixed by the dependent cover
record. -/
theorem sourceClauseD_lTorsionCover_type
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    (E.k_l_torsion_cover.map : S.xK.Hom S.cK) = E.k_quotient.map :=
  E.k_l_torsion_cover_map_eq_quotient

/-- Hence the production l-torsion cover has the core cK as target. -/
theorem sourceClauseD_lTorsionCover_target_is_cK
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    S.cK = S.cKExtension.result :=
  S.cK_eq_extension

/-! ## 4. Paper-target slot S1881: the hybrid coverMap -/

/-- In the S1881 paper-target slot, cK is definitionally the K-core
core.result. -/
theorem s1881_cK_is_core (Slot : S1881D9OrbicurveSlot l) :
    Slot.cK = Slot.core.result :=
  Slot.cK_eq

/-- But that same core is labelled by the (1,l-tors)^± cover type. -/
theorem s1881_cK_label (Slot : S1881D9OrbicurveSlot l) :
    Slot.cK.signature = sourceTypeOneLTorsionPlusMinus l :=
  Slot.cK_signature

/-- The slot xK is labelled by the (1,l-tors) cover type. -/
theorem s1881_xK_label (Slot : S1881D9OrbicurveSlot l) :
    Slot.xK.signature = sourceTypeOneLTorsion l :=
  Slot.xK_signature

/-- The S1881 coverMap has source the (1,l-tors)-labelled xK and target
the core cK = core.result. -/
theorem s1881_coverMap_type (Slot : S1881D9OrbicurveSlot l) :
    (Slot.coverMap : Slot.xK.Hom Slot.cK) = Slot.coverMap :=
  rfl

/-- The target cK cannot be the core X_K of a paper X_K^-> -> X_K
cover: it carries the (1,l-tors)^± label, not (1,1). -/
theorem s1881_cK_not_XK_core (Slot : S1881D9OrbicurveSlot l) :
    Slot.cK.signature ≠ sourceTypeOneOne := by
  rw [Slot.cK_signature]
  exact (sourceTypeOneOne_ne_sourceTypeOneLTorsionPlusMinus l).symm

/-- The source xK cannot be the core X_K either: it carries the
(1,l-tors) label. -/
theorem s1881_xK_not_XK_core (Slot : S1881D9OrbicurveSlot l) :
    Slot.xK.signature ≠ sourceTypeOneOne := by
  rw [Slot.xK_signature]
  exact (sourceTypeOneOne_ne_sourceTypeOneLTorsion l).symm

/-- The target cK cannot be the core C_K of a paper C_K^-> -> C_K
cover: it carries (1,l-tors)^±, not (1,1)^±. -/
theorem s1881_cK_not_CK_core (Slot : S1881D9OrbicurveSlot l) :
    Slot.cK.signature ≠ sourceTypeOneOnePlusMinus := by
  rw [Slot.cK_signature]
  exact (sourceTypeOneOnePlusMinus_ne_sourceTypeOneLTorsionPlusMinus l).symm

/-! ## 5. Generic paper covers and no-go statements -/

/-- A paper X_K^-> -> X_K: an (1,l-tors) object over an (1,1) core. -/
structure S1984PaperXKCover (l : PrimeGeFive) (K : Type u) [Field K] where
  source : Iut.HyperbolicOrbicurve K
  target : Iut.HyperbolicOrbicurve K
  source_type : source.signature = sourceTypeOneLTorsion l
  target_type : target.signature = sourceTypeOneOne
  map : source.Hom target
  finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map

/-- A paper C_K^-> -> C_K: an (1,l-tors)^± object over a (1,1)^± core. -/
structure S1984PaperCKCover (l : PrimeGeFive) (K : Type u) [Field K] where
  source : Iut.HyperbolicOrbicurve K
  target : Iut.HyperbolicOrbicurve K
  source_type : source.signature = sourceTypeOneLTorsionPlusMinus l
  target_type : target.signature = sourceTypeOneOnePlusMinus
  map : source.Hom target
  finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map

/-- No paper X_K^-> -> X_K cover can use the S1881 coverMap with target
cK: the target type would be (1,1), but cK is labelled (1,l-tors)^±. -/
theorem s1881_no_paper_XK_cover_target
    (Slot : S1881D9OrbicurveSlot l)
    (P : S1984PaperXKCover l (S1881A l).K)
    (htgt : P.target = Slot.cK) : False := by
  have h : Slot.cK.signature = sourceTypeOneOne := htgt ▸ P.target_type
  exact (s1881_cK_not_XK_core Slot) h

/-- No paper C_K^-> -> C_K cover can use the S1881 coverMap with target
cK: the target type would be (1,1)^±, but cK is labelled (1,l-tors)^±. -/
theorem s1881_no_paper_CK_cover_target
    (Slot : S1881D9OrbicurveSlot l)
    (P : S1984PaperCKCover l (S1881A l).K)
    (htgt : P.target = Slot.cK) : False := by
  have h : Slot.cK.signature = sourceTypeOneOnePlusMinus :=
    htgt ▸ P.target_type
  exact (s1881_cK_not_CK_core Slot) h

/-- The production k_l_torsion_cover also cannot be a paper X_K^-> -> X_K
cover: its target is the core cK, which is labelled (1,l-tors)^±, not (1,1). -/
theorem sourceClauseD_lTorsionCover_not_paper_XK_cover
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc)
    (P : S1984PaperXKCover l A.K)
    (htgt : P.target = S.cK) : False := by
  have h : S.cK.signature = sourceTypeOneOne := htgt ▸ P.target_type
  exact (sourceSignQuotient_cK_not_XK_core_label S) h

/-- Nor a paper C_K^-> -> C_K cover, for the same target-label reason. -/
theorem sourceClauseD_lTorsionCover_not_paper_CK_cover
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc)
    (P : S1984PaperCKCover l A.K)
    (htgt : P.target = S.cK) : False := by
  have h : S.cK.signature = sourceTypeOneOnePlusMinus :=
    htgt ▸ P.target_type
  exact (sourceSignQuotient_cK_not_core_label S) h

/-- The S1360 K-core identification has the same target conflict: its
coverMap ends at cK, while cK is labelled (1,l-tors)^±. -/
theorem s1360_coverMap_target_not_XK_core
    {X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K}
    (K : S1360KCoreIdentification l X) :
    K.cK.signature ≠ sourceTypeOneOne := by
  rw [K.cK_type]
  exact (sourceTypeOneOne_ne_sourceTypeOneLTorsionPlusMinus l).symm

/-- Likewise it is not a paper C_K^-> -> C_K cover: C_K must be
(1,1)^±, not (1,l-tors)^±. -/
theorem s1360_coverMap_target_not_CK_core
    {X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K}
    (K : S1360KCoreIdentification l X) :
    K.cK.signature ≠ sourceTypeOneOnePlusMinus := by
  rw [K.cK_type]
  exact (sourceTypeOneOnePlusMinus_ne_sourceTypeOneLTorsionPlusMinus l).symm

/-! ## 6. The correct core object, constructed from production data -/

/-- The paper-faithful K-core half: the two core objects, their scalar
extensions, the core equations, and the core quotient X_K -> C_K. -/
structure S1984PaperKCore (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) where
  xK : Iut.HyperbolicOrbicurve A.K
  cK : Iut.HyperbolicOrbicurve A.K
  xKExtension : SourceOrbicurveScalarExtension A.F A.K S.xF
  cKExtension : SourceOrbicurveScalarExtension A.F A.K S.cF
  xK_eq : xK = xKExtension.result
  cK_eq : cK = cKExtension.result
  coreQuotient : xK.Hom cK
  coreQuotient_finiteEtale : Iut.EtaleStackFiniteEtaleMorphism coreQuotient

/-- The production data supplies the paper-faithful core half exactly: the
two scalar extensions, the two core equations, and the sign quotient as the
core map X_K -> C_K. -/
noncomputable def S1984PaperKCore.ofSource
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    S1984PaperKCore l A S where
  xK := S.xK
  cK := S.cK
  xKExtension := S.xKExtension
  cKExtension := S.cKExtension
  xK_eq := S.xK_eq_extension
  cK_eq := S.cK_eq_extension
  coreQuotient := E.k_quotient.map
  coreQuotient_finiteEtale := by
    have h := E.k_l_torsion_cover.finiteEtale
    rw [E.k_l_torsion_cover_map_eq_quotient] at h
    exact h

/-- The core quotient constructed above is exactly the production map named
k_l_torsion_cover. -/
theorem S1984PaperKCore.ofSource_coreQuotient_eq_lTorsionCover
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    (S1984PaperKCore.ofSource (l := l) E).coreQuotient =
      E.k_l_torsion_cover.map := by
  simp [S1984PaperKCore.ofSource, E.k_l_torsion_cover_map_eq_quotient]

/-- The constructed core has the correct object equations. -/
theorem S1984PaperKCore.ofSource_xK_eq
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    (S1984PaperKCore.ofSource (l := l) E).xK =
      S.xKExtension.result :=
  S.xK_eq_extension

theorem S1984PaperKCore.ofSource_cK_eq
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    (S1984PaperKCore.ofSource (l := l) E).cK =
      S.cKExtension.result :=
  S.cK_eq_extension

/-! ## 7. The exact first missing: the actual l-tors cover objects -/

/-- The missing K-side cover half: actual Iut.HyperbolicOrbicurve K objects
X_K^->, C_K^->, their maps to the cores, and the quotient square. -/
structure S1984PaperKCoverData (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) (C : S1984PaperKCore l A S) where
  xArrow : Iut.HyperbolicOrbicurve A.K
  cArrow : Iut.HyperbolicOrbicurve A.K
  xArrow_type : xArrow.signature = sourceTypeOneLTorsion l
  cArrow_type : cArrow.signature = sourceTypeOneLTorsionPlusMinus l
  xArrow_to_xK : xArrow.Hom C.xK
  cArrow_to_cK : cArrow.Hom C.cK
  xArrow_to_cArrow : xArrow.Hom cArrow
  xArrow_to_xK_finiteEtale : Iut.EtaleStackFiniteEtaleMorphism xArrow_to_xK
  cArrow_to_cK_finiteEtale : Iut.EtaleStackFiniteEtaleMorphism cArrow_to_cK
  xArrow_to_cArrow_finiteEtale : Iut.EtaleStackFiniteEtaleMorphism xArrow_to_cArrow

/-- The precise open obligation: construct the cover half over a core. -/
def S1984PaperKCoverMissing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} (C : S1984PaperKCore l A S) : Prop :=
  Nonempty (S1984PaperKCoverData l A S C)

/-- The full paper-faithful K-side chain: core half plus cover half. -/
structure S1984PaperKChain (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) where
  core : S1984PaperKCore l A S
  cover : S1984PaperKCoverData l A S core

/-- The full chain is exactly core plus the missing cover data. -/
theorem S1984PaperKChain_nonempty_iff
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    Nonempty (S1984PaperKChain l A S) ↔
      ∃ C : S1984PaperKCore l A S,
        Nonempty (S1984PaperKCoverData l A S C) := by
  constructor
  · rintro ⟨K⟩
    exact ⟨K.core, ⟨K.cover⟩⟩
  · rintro ⟨C, ⟨D⟩⟩
    exact ⟨⟨C, D⟩⟩

/-! ## 8. The separate SourceOrbicurveObject model is not the stack model -/

/-- Conversion of the bespoke source signature to the actual stack signature. -/
def sourceSignatureToIut (s : SourceOrbicurveSignature) :
    Iut.OrbicurveSignature where
  genus := s.genus
  stackyOrders := s.stackyOrders
  punctures := s.punctures
  stackyOrders_ge_two := s.stackyOrders_ge_two

/-- A lift of the bespoke SourceOrbicurveObject carrier model to the actual
Iut.HyperbolicOrbicurve stack model.  The tree contains no such lift. -/
structure S1984ActualOrbicurveLift {K : Type u} [Field K]
    (X : SourceOrbicurveObject K) where
  actual : Iut.HyperbolicOrbicurve K
  signature : actual.signature = sourceSignatureToIut X.signature

/-- The two SourceCuspDerivedOrbicurves objects are SourceOrbicurveObjects;
their actual-stack lifts are part of the same missing cover half. -/
def S1984DerivedLiftMissing
    {l : PrimeGeFive}
    {D : SourceInitialThetaCandidate l} {Cl : ClauseD l D}
    (X : SourceCuspDerivedOrbicurves l D Cl) : Prop :=
  Nonempty (S1984ActualOrbicurveLift X.xArrow) ∧
    Nonempty (S1984ActualOrbicurveLift X.cArrow)

end LeanFormal.IUT.XiFPaper.S1984KSideObjectAudit
