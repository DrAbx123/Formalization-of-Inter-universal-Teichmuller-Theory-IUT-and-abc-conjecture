import tmp.sheaf.xif.paper.S1881D9D7bActual
import tmp.sheaf.s1984.S1984KSideObjectAudit
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# S1989: the actual K-side cover record for IUT I, Definition 3.1(d)

S1984 audited the production K-side contracts and found:

* `SourceSignQuotientData.xK` and `.cK` are the K-cores
  `X_F x_F K` and `C_F x_F K` (object equations `xK = xKExtension.result`,
  `cK = cKExtension.result`), but they are labelled by the cover types
  `sourceTypeOneLTorsion` and `sourceTypeOneLTorsionPlusMinus`;
* `SourceClauseD.k_l_torsion_cover` is, by its own equation, the sign
  quotient `k_quotient` `X_K -> C_K`, not a degree-`l` cover;
* the S1881 `coverMap : xK.Hom cK` is a hybrid: its source carries the
  cover label, its target is the K-core `cK`.

This file defines the paper-faithful K-side cover record over the actual
production K-core.  It does not modify any production definition and it
does not assert an inhabitant of the record.

The record contains:

* actual `Iut.HyperbolicOrbicurve A.K` objects `xArrow` and `cArrow`,
  with the paper cover signatures `(1,l-tors)` and `(1,l-tors)^pm`;
* a map `xArrow -> xK` and a map `cArrow -> cK` to the two K-cores,
  each finite etale of degree `l`;
* the quotient map `xArrow -> cArrow`, finite etale;
* the quotient square, a 2-isomorphism
  `xArrow -> cArrow -> cK  ~=  xArrow -> xK -> cK`.

The degree-`l` condition is not left as an opaque field.  It is
`StackFiniteEtaleDegree`, defined below using mathlib's
`AlgebraicGeometry.Scheme.Hom.finrank` on every scheme-valued base change
of the representable finite-etale stack morphism.  This makes the degree
condition checkable instead of hidden behind a name.

The paper's first missing construction, in the order of IUT I p.3, is the
actual degree-`l` finite-etale cover `C_K^-> -> C_K` (`CArrowCover`); the
full record additionally requires the X-side cover `X_K^-> -> X_K` and the
quotient square.  No inhabitant is constructed.

The record uses the existing production label constants for the cover
objects.  It does not assert the separate [EtTh] type-name-to-signature
bridge (S1972 M2); that remains a target-level obligation.  The core-label
bridge is isolated separately: the paper-target core labels are
incompatible with the current production labels, and that incompatibility
is proved, not assumed away.

No `sorry`, `admit`, new axiom, `True`, `PUnit`, point-fiber substitution
or terminal-stack substitution is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1989KSideCover

universe u

open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1984KSideObjectAudit
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual

/-! ## 1. A real degree predicate for representable finite-etale stack maps -/

/-- The degree of a finite etale morphism of schemes at a point of its
target, using mathlib's rank of a finite flat morphism.  The flat instance is
derived from etaleness, so the definition is available for every finite
etale map. -/
noncomputable def schemeFiniteEtaleDegree
    {S T : AlgebraicGeometry.Scheme.{u}} (f : S ⟶ T)
    (hFin : AlgebraicGeometry.IsFinite f) (hEt : AlgebraicGeometry.Etale f)
    (t : T) : ℕ :=
  haveI : AlgebraicGeometry.IsFinite f := hFin
  haveI : AlgebraicGeometry.Flat f :=
    (AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.mp hEt).1
  f.finrank t

/-- A representable finite-etale morphism of etale stacks has degree `n`
when every scheme-valued base change is finite etale of rank `n` at every
point of the test scheme. -/
noncomputable def StackFiniteEtaleDegree
    {F : Type u} [Field F]
    {source target : Iut.HyperbolicOrbicurve F}
    (map : source.Hom target)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (n : ℕ) : Prop :=
  ∀ (testScheme : Iut.SchemeOverField F)
    (point : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F testScheme)
      target.stack.fiber)
    (t : testScheme.left),
    schemeFiniteEtaleDegree
      (finiteEtale.baseChange testScheme point).projection.left
      (finiteEtale.hasProperty testScheme point).1
      (finiteEtale.hasProperty testScheme point).2 t = n

/-- The degree predicate is a proposition, not bundled data. -/
theorem stackFiniteEtaleDegree_isProp
    {F : Type u} [Field F]
    {source target : Iut.HyperbolicOrbicurve F}
    (map : source.Hom target)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (n : ℕ) :
    StackFiniteEtaleDegree map finiteEtale n =
      (∀ (testScheme : Iut.SchemeOverField F)
        (point : Pseudofunctor.StrongTrans
          (Iut.schemeRepresentableEtalePseudofunctor F testScheme)
          target.stack.fiber)
        (t : testScheme.left),
        schemeFiniteEtaleDegree
          (finiteEtale.baseChange testScheme point).projection.left
          (finiteEtale.hasProperty testScheme point).1
          (finiteEtale.hasProperty testScheme point).2 t = n) :=
  rfl

/-- The two paper K-side cover labels are different: their stacky-order
lists have different lengths. -/
theorem sourceTypeOneLTorsion_ne_sourceTypeOneLTorsionPlusMinus
    (l : PrimeGeFive) :
    sourceTypeOneLTorsion l ≠ sourceTypeOneLTorsionPlusMinus l := by
  intro h
  have hlen : (sourceTypeOneLTorsion l).stackyOrders.length =
      (sourceTypeOneLTorsionPlusMinus l).stackyOrders.length :=
    congrArg (fun s : Iut.OrbicurveSignature => s.stackyOrders.length) h
  simp [sourceTypeOneLTorsion, sourceTypeOneLTorsionPlusMinus] at hlen

/-! ## 2. The two paper covers over a fixed K-core -/

/-- The paper's `X_K^-> -> X_K`: an actual `(1,l-tors)` hyperbolic
orbicurve over `K` and a finite etale degree-`l` cover to the core `xK`. -/
structure XArrowCover (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) (C : S1984PaperKCore l A S) where
  /-- The actual K-side cover object `X_K^->`. -/
  xArrow : Iut.HyperbolicOrbicurve A.K
  /-- Its paper signature. -/
  xArrow_type : xArrow.signature = sourceTypeOneLTorsion l
  /-- The cover to the K-core `X_K`. -/
  toCore : xArrow.Hom C.xK
  finiteEtale : Iut.EtaleStackFiniteEtaleMorphism toCore
  /-- The cover has degree `l`. -/
  degree : StackFiniteEtaleDegree toCore finiteEtale l.value

/-- The paper's `C_K^-> -> C_K`: an actual `(1,l-tors)^pm` hyperbolic
orbicurve over `K` and a finite etale degree-`l` cover to the core `cK`. -/
structure CArrowCover (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) (C : S1984PaperKCore l A S) where
  /-- The actual K-side cover object `C_K^->`. -/
  cArrow : Iut.HyperbolicOrbicurve A.K
  /-- Its paper signature. -/
  cArrow_type : cArrow.signature = sourceTypeOneLTorsionPlusMinus l
  /-- The cover to the K-core `C_K`. -/
  toCore : cArrow.Hom C.cK
  finiteEtale : Iut.EtaleStackFiniteEtaleMorphism toCore
  /-- The cover has degree `l`. -/
  degree : StackFiniteEtaleDegree toCore finiteEtale l.value

/-! ### 2.1 The production core used by the record -/

/-- The `xK` of the production core is the production `S.xK`. -/
@[simp] theorem ofSource_xK_production
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    (S1984PaperKCore.ofSource E).xK = S.xK := rfl

/-- The `cK` of the production core is the production `S.cK`. -/
@[simp] theorem ofSource_cK_production
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    (S1984PaperKCore.ofSource E).cK = S.cK := rfl

/-! ## 3. The full K-side cover record -/

/-- The paper-faithful K-side cover record over the production K-core.
It contains the two actual cover objects, the two degree-`l` finite-etale
covers to the cores, the quotient map between the cover objects, and the
2-commutative quotient square.

The core `C` is an explicit parameter, exactly as in
`S1984PaperKCoverData`; the production core is obtained by
`S1984PaperKCore.ofSource`. -/
structure KSideCoverActual (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) (C : S1984PaperKCore l A S) where
  /-- The actual `X_K^->`. -/
  xArrow : Iut.HyperbolicOrbicurve A.K
  /-- The actual `C_K^->`. -/
  cArrow : Iut.HyperbolicOrbicurve A.K
  xArrow_type : xArrow.signature = sourceTypeOneLTorsion l
  cArrow_type : cArrow.signature = sourceTypeOneLTorsionPlusMinus l
  /-- The degree-`l` cover `X_K^-> -> X_K`. -/
  xArrow_to_xK : xArrow.Hom C.xK
  xArrow_to_xK_finiteEtale :
    Iut.EtaleStackFiniteEtaleMorphism xArrow_to_xK
  xArrow_to_xK_degree :
    StackFiniteEtaleDegree xArrow_to_xK xArrow_to_xK_finiteEtale l.value
  /-- The degree-`l` cover `C_K^-> -> C_K`. -/
  cArrow_to_cK : cArrow.Hom C.cK
  cArrow_to_cK_finiteEtale :
    Iut.EtaleStackFiniteEtaleMorphism cArrow_to_cK
  cArrow_to_cK_degree :
    StackFiniteEtaleDegree cArrow_to_cK cArrow_to_cK_finiteEtale l.value
  /-- The quotient map `X_K^-> -> C_K^->`. -/
  xArrow_to_cArrow : xArrow.Hom cArrow
  xArrow_to_cArrow_finiteEtale :
    Iut.EtaleStackFiniteEtaleMorphism xArrow_to_cArrow
  /-- The quotient square: the two ways around the square agree up to a
  2-isomorphism. -/
  quotientSquare :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp xArrow_to_cArrow cArrow_to_cK)
      (Iut.HyperbolicOrbicurve.Hom.comp xArrow_to_xK C.coreQuotient)

namespace KSideCoverActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : S1984PaperKCore l A S}

/-- The X-side half of the record. -/
def toXArrowCover (K : KSideCoverActual l A S C) :
    XArrowCover l A S C where
  xArrow := K.xArrow
  xArrow_type := K.xArrow_type
  toCore := K.xArrow_to_xK
  finiteEtale := K.xArrow_to_xK_finiteEtale
  degree := K.xArrow_to_xK_degree

/-- The C-side half of the record. -/
def toCArrowCover (K : KSideCoverActual l A S C) :
    CArrowCover l A S C where
  cArrow := K.cArrow
  cArrow_type := K.cArrow_type
  toCore := K.cArrow_to_cK
  finiteEtale := K.cArrow_to_cK_finiteEtale
  degree := K.cArrow_to_cK_degree

/-- The record refines the S1984 paper cover data by forgetting the
quotient square and the degree certificates. -/
def toS1984PaperKCoverData (K : KSideCoverActual l A S C) :
    S1984PaperKCoverData l A S C where
  xArrow := K.xArrow
  cArrow := K.cArrow
  xArrow_type := K.xArrow_type
  cArrow_type := K.cArrow_type
  xArrow_to_xK := K.xArrow_to_xK
  cArrow_to_cK := K.cArrow_to_cK
  xArrow_to_cArrow := K.xArrow_to_cArrow
  xArrow_to_xK_finiteEtale := K.xArrow_to_xK_finiteEtale
  cArrow_to_cK_finiteEtale := K.cArrow_to_cK_finiteEtale
  xArrow_to_cArrow_finiteEtale := K.xArrow_to_cArrow_finiteEtale

/-- Reassemble the record from exactly its two covers, the quotient map and
the quotient square.  No extra data is hidden in the record. -/
def ofCovers (XC : XArrowCover l A S C) (CC : CArrowCover l A S C)
    (q : XC.xArrow.Hom CC.cArrow)
    (qFiniteEtale : Iut.EtaleStackFiniteEtaleMorphism q)
    (square :
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp q CC.toCore)
        (Iut.HyperbolicOrbicurve.Hom.comp XC.toCore C.coreQuotient)) :
    KSideCoverActual l A S C where
  xArrow := XC.xArrow
  cArrow := CC.cArrow
  xArrow_type := XC.xArrow_type
  cArrow_type := CC.cArrow_type
  xArrow_to_xK := XC.toCore
  xArrow_to_xK_finiteEtale := XC.finiteEtale
  xArrow_to_xK_degree := XC.degree
  cArrow_to_cK := CC.toCore
  cArrow_to_cK_finiteEtale := CC.finiteEtale
  cArrow_to_cK_degree := CC.degree
  xArrow_to_cArrow := q
  xArrow_to_cArrow_finiteEtale := qFiniteEtale
  quotientSquare := square

@[simp] theorem ofCovers_xArrow (XC : XArrowCover l A S C)
    (CC : CArrowCover l A S C)
    (q : XC.xArrow.Hom CC.cArrow)
    (qFiniteEtale : Iut.EtaleStackFiniteEtaleMorphism q)
    (square : Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp q CC.toCore)
      (Iut.HyperbolicOrbicurve.Hom.comp XC.toCore C.coreQuotient)) :
    (ofCovers XC CC q qFiniteEtale square).xArrow = XC.xArrow := rfl

/-- The two cover objects are genuinely different: their paper signatures
are different. -/
theorem xArrow_ne_cArrow (K : KSideCoverActual l A S C) :
    K.xArrow ≠ K.cArrow := by
  intro h
  have hs : K.xArrow.signature = K.cArrow.signature := congrArg _ h
  rw [K.xArrow_type, K.cArrow_type] at hs
  exact sourceTypeOneLTorsion_ne_sourceTypeOneLTorsionPlusMinus l hs

end KSideCoverActual

/-! ## 4. The exact missing propositions -/

/-- The X-side cover is missing: no actual degree-`l` finite-etale cover
`X_K^-> -> X_K` is constructed in this file. -/
def XArrowCoverMissing (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) (C : S1984PaperKCore l A S) : Prop :=
  Nonempty (XArrowCover l A S C)

/-- The C-side cover is missing: no actual degree-`l` finite-etale cover
`C_K^-> -> C_K` is constructed in this file.  This is the paper's initial
K-side cover (IUT I, p.3), hence the first missing construction at the
orbicurve-cover level. -/
def CArrowCoverMissing (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) (C : S1984PaperKCore l A S) : Prop :=
  Nonempty (CArrowCover l A S C)

/-- The full K-side cover record is missing.  This is the exact open
obligation; it is not asserted. -/
def KSideCoverMissing (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) (C : S1984PaperKCore l A S) : Prop :=
  Nonempty (KSideCoverActual l A S C)

/-- The full record requires the C-side cover. -/
theorem KSideCoverMissing.cArrowCoverMissing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : S1984PaperKCore l A S}
    (h : KSideCoverMissing l A S C) : CArrowCoverMissing l A S C := by
  rcases h with ⟨K⟩
  exact ⟨K.toCArrowCover⟩

/-- The full record requires the X-side cover. -/
theorem KSideCoverMissing.xArrowCoverMissing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : S1984PaperKCore l A S}
    (h : KSideCoverMissing l A S C) : XArrowCoverMissing l A S C := by
  rcases h with ⟨K⟩
  exact ⟨K.toXArrowCover⟩

/-- The record is exactly the two covers, the quotient map and the
quotient square.  This is the precise decomposition of the missing data: the
record is nonempty if and only if the two degree-`l` covers exist, admit a
finite-etale quotient map between them, and the quotient square is
2-commutative. -/
theorem KSideCoverMissing_iff :
    KSideCoverMissing l A S C ↔
      ∃ (XC : XArrowCover l A S C) (CC : CArrowCover l A S C),
        ∃ (q : XC.xArrow.Hom CC.cArrow)
          (qFiniteEtale : Iut.EtaleStackFiniteEtaleMorphism q),
          Nonempty
            (Iut.HyperbolicOrbicurve.Hom.TwoIso
              (Iut.HyperbolicOrbicurve.Hom.comp q CC.toCore)
              (Iut.HyperbolicOrbicurve.Hom.comp XC.toCore C.coreQuotient)) := by
  constructor
  · rintro ⟨K⟩
    exact ⟨K.toXArrowCover, K.toCArrowCover, K.xArrow_to_cArrow,
      K.xArrow_to_cArrow_finiteEtale, ⟨K.quotientSquare⟩⟩
  · rintro ⟨XC, CC, q, qFiniteEtale, ⟨square⟩⟩
    exact ⟨KSideCoverActual.ofCovers XC CC q qFiniteEtale square⟩

/-! ## 5. The production cover cannot be reused as either l-tors cover -/

/-- A C-side cover object can never be the production core `xK`: the cover
object is labelled `(1,l-tors)^pm`, while `xK` is labelled `(1,l-tors)`. -/
theorem cArrowCover_source_ne_xK
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : S1984PaperKCore l A S}
    (K : CArrowCover l A S C) : K.cArrow ≠ S.xK := by
  intro h
  have hlabel : K.cArrow.signature = sourceTypeOneLTorsionPlusMinus l :=
    K.cArrow_type
  rw [h, S.xKType] at hlabel
  exact sourceTypeOneLTorsion_ne_sourceTypeOneLTorsionPlusMinus l hlabel

/-- The production core `xK` and the production core `cK` are different:
their labels are different.  In particular the production
`k_l_torsion_cover` has target `cK`, not the X-side core `xK`. -/
theorem ofSource_xK_ne_cK
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    (S1984PaperKCore.ofSource E).xK ≠ S.cK := by
  intro h
  have hs : S.xK.signature = S.cK.signature := by
    simpa [S1984PaperKCore.ofSource] using
      congrArg (fun X : Iut.HyperbolicOrbicurve A.K => X.signature) h
  rw [S.xKType, S.cKType] at hs
  exact sourceTypeOneLTorsion_ne_sourceTypeOneLTorsionPlusMinus l hs

/-- The production `k_l_torsion_cover` has target `cK`, which is not the
X-side core `xK`. -/
theorem sourceClauseD_lTorsionCover_target_ne_xK
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    S.cK ≠ (S1984PaperKCore.ofSource E).xK :=
  (ofSource_xK_ne_cK E).symm

/-- The production `k_l_torsion_cover` has source `xK`, which cannot be
the source object of the C-side cover. -/
theorem sourceClauseD_lTorsionCover_source_ne_cArrow
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc)
    (K : CArrowCover l A S (S1984PaperKCore.ofSource E)) :
    S.xK ≠ K.cArrow :=
  (cArrowCover_source_ne_xK K).symm

/-! ## 6. The label bridge is incompatible with the production core labels -/

/-- The paper-target core labels used by S1984: `(1,1)` for `X_K` and
`(1,1)^pm` for `C_K`.  These are the labels of the S1984 target, not the
honest S1972 numeric signatures; changing the numeric labels is a separate
target decision. -/
def CoreLabelBridge {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} (C : S1984PaperKCore l A S) : Prop :=
  C.xK.signature = sourceTypeOneOne ∧
    C.cK.signature = sourceTypeOneOnePlusMinus

/-- The label bridge fails for the core constructed from production data:
the production core objects carry the l-tors cover labels, not the core
labels.  This is a theorem, not a missing hypothesis. -/
theorem coreLabelBridge_ofSource_false
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    ¬ CoreLabelBridge (S1984PaperKCore.ofSource E) := by
  rintro ⟨hx, hc⟩
  exact sourceSignQuotient_xK_not_core_label S hx

/-- A fully paper-faithful K-side record: the cover record plus the core
label bridge.  This is the shape one would need for a paper-faithful
restatement of Definition 3.1(d). -/
structure PaperFaithfulKSide (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) (C : S1984PaperKCore l A S) where
  cover : KSideCoverActual l A S C
  coreLabelBridge : CoreLabelBridge C

/-- Over the production core, the fully paper-faithful K-side record is
empty, independently of whether the cover data exist: the core labels are
already incompatible.  A retyping of the core labels (a target decision) is
therefore a prerequisite, not a consequence of constructing the covers. -/
theorem paperFaithfulKSide_ofSource_empty
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    ¬ Nonempty (PaperFaithfulKSide l A S (S1984PaperKCore.ofSource E)) := by
  rintro ⟨K⟩
  exact coreLabelBridge_ofSource_false E K.coreLabelBridge

/-! ## 7. The S1881 hybrid endpoints are not the two paper covers -/

/-- The S1881 slot's `xK` endpoint is labelled `(1,l-tors)`, so it cannot
be the source object `cArrow` of the C-side cover, which is labelled
`(1,l-tors)^pm`. -/
theorem s1881_xK_label_not_cArrow
    {l : PrimeGeFive} (Slot : S1881D9OrbicurveSlot l) :
    Slot.xK.signature ≠ sourceTypeOneLTorsionPlusMinus l := by
  rw [Slot.xK_signature]
  exact sourceTypeOneLTorsion_ne_sourceTypeOneLTorsionPlusMinus l

/-- The S1881 slot's `cK` endpoint is labelled `(1,l-tors)^pm`, so it
cannot be the target object `xK` of the X-side cover, which is labelled
`(1,l-tors)`. -/
theorem s1881_cK_label_not_xK
    {l : PrimeGeFive} (Slot : S1881D9OrbicurveSlot l) :
    Slot.cK.signature ≠ sourceTypeOneLTorsion l := by
  rw [Slot.cK_signature]
  exact (sourceTypeOneLTorsion_ne_sourceTypeOneLTorsionPlusMinus l).symm

/-- The S1881 `coverMap : xK.Hom cK` has the wrong source for the C-side
cover and the wrong target for the X-side cover.  It is therefore not either
of the two paper K-side covers; the label mismatch is proved here, not
assumed. -/
theorem s1881_coverMap_endpoints_not_paper_covers
    {l : PrimeGeFive} (Slot : S1881D9OrbicurveSlot l) :
    Slot.xK.signature ≠ sourceTypeOneLTorsionPlusMinus l ∧
      Slot.cK.signature ≠ sourceTypeOneLTorsion l :=
  ⟨s1881_xK_label_not_cArrow Slot, s1881_cK_label_not_xK Slot⟩

end LeanFormal.IUT.XiFPaper.S1989KSideCover