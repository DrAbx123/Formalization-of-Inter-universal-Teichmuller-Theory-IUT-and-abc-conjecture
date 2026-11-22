import tmp.sheaf.xif.paper.S1881D9D7bActual

/-!
# S1886: the D9 orbicurve slot over the actual S1732 line, and its exact first missing

S1881 reduces the D9 orbicurve input of the S1732 contract to the structure
`S1881D9OrbicurveSlot l` with fields

* `cF` of paper type `(1,1)^pm`;
* its K-core scalar extension `core` and `cK = core.result` of type `(1,l-tors)^pm`;
* `xK` of type `(1,l-tors)`, the finite-etale cover `xK -> cK`;
* the certified orbifold fundamental-group datum of `xK` over `G_K`.

This file inserts no object and no signature.  It proves:

* the slot is definitionally the sigma type of its first field `C : S1881CF l`
  and the remaining tail (`S1886D9SlotEquiv`); it is nonempty exactly when
  a first field with a tail exists (`S1886D9Slot_nonempty_iff`);
* the tail is exactly a K-core scalar extension whose result has the
  `(1,l-tors)^pm` signature (and the K-core stack must genuinely differ:
  `S1886KCore_stack_ne`), plus an actual `(1,l-tors)` orbicurve `X_K`,
  the bundled finite-etale cover `X_K -> C_K`, and its group data
  (`S1886D9SlotTail_nonempty_iff`).  Every slot supplies all of them
  (`S1886KCoreOfSlot`, `S1886XKCoverDataOfSlot`);
* the first field cannot be the already constructed actual S1726 orbicurve,
  and cannot reuse its stack: the S1726 stack carries the once-punctured
  `(1,1)` signature, not `(1,1)^pm` (`S1886FirstField_stack_ne_s1726`,
  `S1886NoSlotWithS1726`).

## The exact first missing

The literal type `S1881CF l` is *not* the honest obstruction: since
`Iut.HyperbolicOrbicurve` stores the signature as metadata on the stack,
inserting the `(1,1)^pm` label on the actual S1726 fiber already inhabits it
(`S1886CFMetadataRelabel`).  That object is a relabeling, not the paper's
quotient `C_F = X_F/{+-1}`; it is recorded only to show that the literal
first-field type is too weak.

The paper-faithful first missing is therefore `S1886PaperCF l`: the actual
sign quotient of the actual S1726 orbicurve -- an
`Iut.OrbicurveSignAction` on `S1726Orbicurve`, the sign-invariant quotient
morphism to `C_F`, the universal property
`Iut.OrbicurveSignQuotientWitness`, and `C_F.signature = (1,1)^pm`.
Its own first field is the geometric `[-1]` endomorphism
`S1726Orbicurve.Hom S1726Orbicurve` (`S1886EllipticInvolutionMissing`).
The tree contains only the curve-point involution (S1555/S1633 on the
Gaussian line), never the stack lift, so no `OrbicurveSignAction`, quotient
or quotient witness can be constructed.

Given the paper `C_F`, the remaining missing data are, in order: the K-core
scalar extension (`S1886KCore`), the orbicurve `X_K` together with the
finite-etale cover to `C_K` (`S1886XKCoverData`), and the orbifold
fundamental-group datum.  `S1886D9OrbicurveSlotOfData` fills the S1881 slot
from exactly these data and nothing else.

No True, PUnit, arbitrary group, arbitrary proposition, sorry, admit or new
axiom is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1886D9OrbicurveActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual

/-! ## 1. The actual field deck of the S1732 line -/

/-- The F-side field of the actual line. -/
abbrev S1886F (l : PrimeGeFive) : Type := (S1732A l).F

/-- The K-side field of the actual line. -/
abbrev S1886K (l : PrimeGeFive) : Type := (S1732A l).K

/-- The absolute Galois group used by the D9 group datum. -/
abbrev S1886Galois (l : PrimeGeFive) : ProfiniteGrp :=
  Iut.AbsoluteGaloisProfinite (S1886K l)

/-- On the actual S1732 line the base field and the K-field are the same. -/
theorem S1886F_eq_K (l : PrimeGeFive) : S1886F l = S1886K l := rfl

/-- The actual line is the S1726 line: the S1726 orbicurve lives over this F. -/
theorem S1886F_eq_S1726K (l : PrimeGeFive) : S1886F l = S1726K := rfl

/-! ## 2. The exact tail of the S1881 D9 orbicurve slot -/

/-- Everything in `S1881D9OrbicurveSlot` after the first field `cF`.
The fields are literally the remaining fields of the S1881 slot, so the
decomposition below is definitional. -/
structure S1886D9SlotTail (l : PrimeGeFive) (C : S1881CF l) where
  /-- The K-core scalar extension of the first field. -/
  core : SourceOrbicurveScalarExtension (S1732A l).F (S1732A l).K C.1
  /-- The K-side quotient C_K, of type (1,l-tors)^pm. -/
  cK : Iut.HyperbolicOrbicurve (S1732A l).K
  cK_eq : cK = core.result
  cK_signature : cK.signature = sourceTypeOneLTorsionPlusMinus l
  /-- The l-torsion cover X_K, of type (1,l-tors). -/
  xK : Iut.HyperbolicOrbicurve (S1732A l).K
  xK_signature : xK.signature = sourceTypeOneLTorsion l
  /-- The finite-etale cover X_K -> C_K. -/
  coverMap : xK.Hom cK
  coverFiniteEtale : Iut.EtaleStackFiniteEtaleMorphism coverMap
  /-- Certified orbifold fundamental-group data of X_K over G_K. -/
  groups : Iut.OrbicurveFundamentalGroupData xK (S1886Galois l)

/-- The S1881 D9 orbicurve slot is definitionally its first field together
with the tail. -/
noncomputable def S1886D9SlotEquiv (l : PrimeGeFive) :
    S1881D9OrbicurveSlot l ≃
      Σ C : S1881CF l, S1886D9SlotTail l C where
  toFun S :=
    ⟨S1881D9OrbicurveSlot.firstField l S,
      { core := S.core
        cK := S.cK
        cK_eq := S.cK_eq
        cK_signature := S.cK_signature
        xK := S.xK
        xK_signature := S.xK_signature
        coverMap := S.coverMap
        coverFiniteEtale := S.coverFiniteEtale
        groups := S.groups }⟩
  invFun p :=
    { cF := p.1.1
      cF_signature := p.1.2
      core := p.2.core
      cK := p.2.cK
      cK_eq := p.2.cK_eq
      cK_signature := p.2.cK_signature
      xK := p.2.xK
      xK_signature := p.2.xK_signature
      coverMap := p.2.coverMap
      coverFiniteEtale := p.2.coverFiniteEtale
      groups := p.2.groups }
  left_inv S := by
    cases S
    rfl
  right_inv p := by
    rcases p with ⟨⟨cF, h⟩, t⟩
    cases t
    rfl

/-- The S1881 slot is nonempty exactly when some first field carries a tail. -/
theorem S1886D9Slot_nonempty_iff (l : PrimeGeFive) :
    Nonempty (S1881D9OrbicurveSlot l) ↔
      ∃ C : S1881CF l, Nonempty (S1886D9SlotTail l C) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S1881D9OrbicurveSlot.firstField l S, ⟨(S1886D9SlotEquiv l S).2⟩⟩
  · rintro ⟨C, ⟨T⟩⟩
    exact ⟨(S1886D9SlotEquiv l).symm ⟨C, T⟩⟩

/-! ## 3. The tail decomposed: K-core, X_K cover, groups -/

/-- The K-core datum of the D9 slot: the actual scalar extension of C_F whose
result carries the K-side `(1,l-tors)^pm` signature. -/
structure S1886KCore (l : PrimeGeFive) (C : S1881CF l) where
  core : SourceOrbicurveScalarExtension (S1732A l).F (S1732A l).K C.1
  signature : core.result.signature = sourceTypeOneLTorsionPlusMinus l

/-- The residual D9 data after the K-core has been fixed: an actual
`(1,l-tors)` orbicurve X_K, the bundled finite-etale cover to C_K, and the
certified orbifold fundamental-group datum over G_K. -/
structure S1886XKCoverData (l : PrimeGeFive) (C : S1881CF l)
    (K : S1886KCore l C) where
  xK : Iut.HyperbolicOrbicurve (S1732A l).K
  xK_signature : xK.signature = sourceTypeOneLTorsion l
  cover : SourceOrbicurveFiniteEtaleCover xK K.core.result
  groups : Iut.OrbicurveFundamentalGroupData xK (S1886Galois l)

/-- The K-core part of a tail. -/
noncomputable def S1886D9SlotTail.toKCore {l : PrimeGeFive} {C : S1881CF l}
    (T : S1886D9SlotTail l C) : S1886KCore l C where
  core := T.core
  signature := by
    rw [← T.cK_eq]
    exact T.cK_signature

/-- The X_K/cover/groups part of a tail, over the extracted K-core. -/
noncomputable def S1886D9SlotTail.toXKCoverData {l : PrimeGeFive} {C : S1881CF l}
    (T : S1886D9SlotTail l C) :
    S1886XKCoverData l C (S1886D9SlotTail.toKCore T) where
  xK := T.xK
  xK_signature := T.xK_signature
  cover :=
    T.cK_eq ▸
      ({ map := T.coverMap
         finiteEtale := T.coverFiniteEtale } :
        SourceOrbicurveFiniteEtaleCover T.xK T.cK)
  groups := T.groups

/-- Conversely, the K-core plus the X_K/cover/groups data give the tail. -/
noncomputable def S1886D9SlotTail.ofKCoreData {l : PrimeGeFive} {C : S1881CF l}
    (K : S1886KCore l C) (D : S1886XKCoverData l C K) :
    S1886D9SlotTail l C where
  core := K.core
  cK := K.core.result
  cK_eq := rfl
  cK_signature := K.signature
  xK := D.xK
  xK_signature := D.xK_signature
  coverMap := D.cover.map
  coverFiniteEtale := D.cover.finiteEtale
  groups := D.groups

/-- Exact decomposition of the tail: K-core plus X_K cover data. -/
theorem S1886D9SlotTail_nonempty_iff {l : PrimeGeFive} (C : S1881CF l) :
    Nonempty (S1886D9SlotTail l C) ↔
      ∃ K : S1886KCore l C, Nonempty (S1886XKCoverData l C K) := by
  constructor
  · rintro ⟨T⟩
    exact ⟨S1886D9SlotTail.toKCore T,
      ⟨S1886D9SlotTail.toXKCoverData T⟩⟩
  · rintro ⟨K, ⟨D⟩⟩
    exact ⟨S1886D9SlotTail.ofKCoreData K D⟩

/-- Exact decomposition of the S1881 D9 orbicurve slot: a first field C_F, a
K-core, and the X_K/cover/groups data. -/
theorem S1886D9OrbicurveSlot_nonempty_iff (l : PrimeGeFive) :
    Nonempty (S1881D9OrbicurveSlot l) ↔
      ∃ C : S1881CF l, ∃ K : S1886KCore l C,
        Nonempty (S1886XKCoverData l C K) := by
  rw [S1886D9Slot_nonempty_iff]
  constructor
  · rintro ⟨C, hT⟩
    obtain ⟨K, hD⟩ := (S1886D9SlotTail_nonempty_iff C).mp hT
    exact ⟨C, K, hD⟩
  · rintro ⟨C, K, hD⟩
    exact ⟨C, (S1886D9SlotTail_nonempty_iff C).mpr ⟨K, hD⟩⟩

/-- Filling the S1881 D9 orbicurve slot from exactly: a first field C_F, a
K-core of C_F, and the X_K/cover/groups data. -/
noncomputable def S1886D9OrbicurveSlotOfData {l : PrimeGeFive} (C : S1881CF l)
    (K : S1886KCore l C) (D : S1886XKCoverData l C K) :
    S1881D9OrbicurveSlot l :=
  (S1886D9SlotEquiv l).symm ⟨C, S1886D9SlotTail.ofKCoreData K D⟩

@[simp] theorem S1886D9OrbicurveSlotOfData_cF {l : PrimeGeFive}
    (C : S1881CF l) (K : S1886KCore l C) (D : S1886XKCoverData l C K) :
    (S1886D9OrbicurveSlotOfData C K D).cF = C.1 := rfl

@[simp] theorem S1886D9OrbicurveSlotOfData_cK {l : PrimeGeFive}
    (C : S1881CF l) (K : S1886KCore l C) (D : S1886XKCoverData l C K) :
    (S1886D9OrbicurveSlotOfData C K D).cK = K.core.result := rfl

@[simp] theorem S1886D9OrbicurveSlotOfData_xK {l : PrimeGeFive}
    (C : S1881CF l) (K : S1886KCore l C) (D : S1886XKCoverData l C K) :
    (S1886D9OrbicurveSlotOfData C K D).xK = D.xK := rfl

/-! ## 4. Genuine stack-change constraints

The K-side signatures force the K-core, C_K and X_K to live on stacks that
differ from the F-side stack.  In particular no identity or stack-preserving
"K-core" can fill the slot. -/

/-- The K-core stack differs from the F-side stack: otherwise the two
orbicurves would advertise the same signature. -/
theorem S1886KCore_stack_ne {l : PrimeGeFive} {C : S1881CF l}
    (K : S1886KCore l C) : K.core.result.stack ≠ C.1.stack := by
  intro h
  have hs : K.core.result.signature = C.1.signature :=
    Iut.HyperbolicOrbicurve.signature_eq_of_stack_eq h
  exact S1881TypeOneOnePlusMinus_ne_typeOneLTorsionPlusMinus l
    (C.2.symm.trans (hs.symm.trans K.signature))

/-- The cover target C_K lives on a stack different from the F-side stack. -/
theorem S1886KCore_cK_stack_ne {l : PrimeGeFive} {C : S1881CF l}
    (K : S1886KCore l C) (cK : Iut.HyperbolicOrbicurve (S1732A l).K)
    (hcK : cK = K.core.result)
    (hcK_signature : cK.signature = sourceTypeOneLTorsionPlusMinus l) :
    cK.stack ≠ C.1.stack := by
  subst hcK
  exact S1886KCore_stack_ne K

/-- X_K lives on a stack different from C_K: the two signatures differ. -/
theorem S1886XKCoverData_xK_stack_ne {l : PrimeGeFive} {C : S1881CF l}
    {K : S1886KCore l C} (D : S1886XKCoverData l C K) :
    D.xK.stack ≠ K.core.result.stack := by
  intro h
  have hs : D.xK.signature = K.core.result.signature :=
    Iut.HyperbolicOrbicurve.signature_eq_of_stack_eq h
  exact S1881TypeOneLTorsion_ne_typeOneLTorsionPlusMinus l
    (D.xK_signature.symm.trans (hs.trans K.signature))

/-- The cover map X_K -> C_K is a cover of distinct orbicurves: the source and
target of the slot's finite-etale cover are different objects. -/
theorem S1886D9SlotTail_xK_ne_cK {l : PrimeGeFive} {C : S1881CF l}
    (T : S1886D9SlotTail l C) : T.xK ≠ T.cK := by
  intro h
  have hs : T.xK.signature = T.cK.signature := congrArg _ h
  exact S1881TypeOneLTorsion_ne_typeOneLTorsionPlusMinus l
    (T.xK_signature.symm.trans (hs.trans T.cK_signature))

/-! ## 4b. Signature and genus arithmetic forced by the slot -/

/-- The first field has genus one, as forced by the paper type `(1,1)^pm`. -/
theorem S1886FirstField_genus (l : PrimeGeFive) (C : S1881CF l) :
    C.1.signature.genus = 1 := by
  rw [C.2]
  rfl

/-- The K-core preserves the genus of the first field. -/
theorem S1886KCore_genus {l : PrimeGeFive} {C : S1881CF l}
    (K : S1886KCore l C) : K.core.result.signature.genus = 1 := by
  rw [K.core.genus_preserved, S1886FirstField_genus l C]

/-- The K-core signature differs from the F-side `(1,1)^pm` signature: the
K-core is a genuine change of decoration, not a relabeling of the same
signature. -/
theorem S1886KCore_signature_ne {l : PrimeGeFive} {C : S1881CF l}
    (K : S1886KCore l C) : K.core.result.signature ≠ C.1.signature := by
  intro h
  exact S1881TypeOneOnePlusMinus_ne_typeOneLTorsionPlusMinus l
    (C.2.symm.trans (h.symm.trans K.signature))

/-- The `l`-torsion cover has genus one. -/
theorem S1886XKCoverData_xK_genus {l : PrimeGeFive} {C : S1881CF l}
    {K : S1886KCore l C} (D : S1886XKCoverData l C K) :
    D.xK.signature.genus = 1 := by
  rw [D.xK_signature]
  rfl

/-! ## 5. Extraction of the exact data from any slot -/

/-- The first field of the slot. -/
noncomputable def S1886FirstFieldOfSlot {l : PrimeGeFive}
    (S : S1881D9OrbicurveSlot l) : S1881CF l :=
  S1881D9OrbicurveSlot.firstField l S

@[simp] theorem S1886FirstFieldOfSlot_val {l : PrimeGeFive}
    (S : S1881D9OrbicurveSlot l) : (S1886FirstFieldOfSlot S).1 = S.cF := rfl

/-- The exact K-core dictionary of any slot. -/
noncomputable def S1886KCoreOfSlot {l : PrimeGeFive}
    (S : S1881D9OrbicurveSlot l) : S1886KCore l (S1886FirstFieldOfSlot S) :=
  S1886D9SlotTail.toKCore (S1886D9SlotEquiv l S).2

@[simp] theorem S1886KCoreOfSlot_core {l : PrimeGeFive}
    (S : S1881D9OrbicurveSlot l) :
    (S1886KCoreOfSlot S).core = S.core := rfl

/-- The exact X_K/cover/groups dictionary of any slot. -/
noncomputable def S1886XKCoverDataOfSlot {l : PrimeGeFive}
    (S : S1881D9OrbicurveSlot l) :
    S1886XKCoverData l (S1886FirstFieldOfSlot S) (S1886KCoreOfSlot S) :=
  S1886D9SlotTail.toXKCoverData (S1886D9SlotEquiv l S).2

@[simp] theorem S1886XKCoverDataOfSlot_xK {l : PrimeGeFive}
    (S : S1881D9OrbicurveSlot l) : (S1886XKCoverDataOfSlot S).xK = S.xK := rfl

/-- The exact finite-etale cover `X_K -> C_K` carried by any slot. -/
noncomputable def S1886FiniteEtaleCoverOfSlot {l : PrimeGeFive}
    (S : S1881D9OrbicurveSlot l) :
    SourceOrbicurveFiniteEtaleCover S.xK S.cK where
  map := S.coverMap
  finiteEtale := S.coverFiniteEtale

/-- The exact group datum of any slot, as the source orbicurve group record. -/
noncomputable def S1886GroupDataOfSlot {l : PrimeGeFive}
    (S : S1881D9OrbicurveSlot l) :
    SourceOrbicurveGroupData S.xK (S1886Galois l) where
  groups := S.groups

/-- The certified profinite exact sequence of the D9 group datum. -/
noncomputable def S1886ExactSequenceOfSlot {l : PrimeGeFive}
    (S : S1881D9OrbicurveSlot l) :
    Iut.ProfiniteFundamentalExactSequence S.groups.geometric.group
      S.groups.arithmetic.group (S1886Galois l) :=
  S.groups.exactSequence

/-- The arithmetic projection of the D9 group datum is surjective. -/
theorem S1886ProjectionSurjectiveOfSlot {l : PrimeGeFive}
    (S : S1881D9OrbicurveSlot l) :
    Function.Surjective S.groups.projection :=
  S.groups.projection_surjective

/-! ## 6. The actual S1726 orbicurve is not the first field -/

/-- No inhabitant of the literal first field shares the actual S1726 stack:
the S1726 stack's stored signature is the once-punctured `(1,1)` one. -/
theorem S1886FirstField_stack_ne_s1726 (l : PrimeGeFive) (C : S1881CF l) :
    C.1.stack ≠ S1726Orbicurve.stack := by
  intro h
  have hs : C.1.signature = S1726Orbicurve.signature :=
    Iut.HyperbolicOrbicurve.signature_eq_of_stack_eq h
  exact S1881OncePunctured_ne_typeOneOnePlusMinus
    (C.2.symm.trans (hs.trans S1726Orbicurve_signature)).symm

/-- The actual S1726 orbicurve itself is not an inhabitant of the first
field: its signature is the once-punctured `(1,1)` one. -/
theorem S1886FirstField_ne_s1726 (l : PrimeGeFive) (C : S1881CF l) :
    C.1 ≠ S1726Orbicurve := by
  intro h
  exact S1886FirstField_stack_ne_s1726 l C (by rw [h])

/-- No S1881 D9 orbicurve slot can have the actual S1726 orbicurve as its
F-side quotient. -/
theorem S1886NoSlotWithS1726 (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) : S.cF ≠ S1726Orbicurve := by
  intro h
  have hs : S1726Orbicurve.signature = sourceTypeOneOnePlusMinus := by
    rw [← h]
    exact S.cF_signature
  rw [S1726Orbicurve_signature] at hs
  exact S1881OncePunctured_ne_typeOneOnePlusMinus hs

/-- Likewise the K-side quotient of a slot is not the S1726 orbicurve. -/
theorem S1886Slot_cK_ne_s1726 (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) : S.cK ≠ S1726Orbicurve := by
  intro h
  have hs : S.cK.signature = S1726Orbicurve.signature := congrArg _ h
  have h2 : S1726Orbicurve.signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
    S1726Orbicurve_signature
  rw [S.cK_signature] at hs
  exact S1881OncePunctured_ne_typeOneLTorsionPlusMinus l
    (hs.trans h2).symm

/-- And the `(1,l-tors)` cover of a slot is not the S1726 orbicurve. -/
theorem S1886Slot_xK_ne_s1726 (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) : S.xK ≠ S1726Orbicurve := by
  intro h
  have hs : S.xK.signature = S1726Orbicurve.signature := congrArg _ h
  have h2 : S1726Orbicurve.signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
    S1726Orbicurve_signature
  rw [S.xK_signature] at hs
  exact S1881OncePunctured_ne_typeOneLTorsion l (hs.trans h2).symm

/-! ## 7. The paper-faithful first missing: the actual sign quotient -/

/-- The exact first missing geometric object of the paper's C_F: the geometric
`[-1]` endomorphism of the actual S1726 orbicurve.  (`HyperbolicOrbicurve.Hom`
is a morphism of represented etale stacks, not a map of curve points.) -/
abbrev S1886EllipticInvolutionMissing (l : PrimeGeFive) : Type 1 :=
  @Iut.HyperbolicOrbicurve.Hom S1726K _ S1726Orbicurve S1726Orbicurve

/-- The paper-faithful first missing datum: the actual sign quotient
`C_F = X_F/{+-1}` of the actual S1726 orbicurve, with the `(1,1)^pm`
signature.  The universal property is the genuine quotient property of
`Iut.OrbicurveSignQuotientWitness`, so the target is tied to the actual
S1726 stack rather than being an arbitrary signature relabeling. -/
structure S1886PaperCF (l : PrimeGeFive) where
  /-- The coherent `{+-1}` action on the actual S1726 orbicurve. -/
  action : Iut.OrbicurveSignAction S1726Orbicurve
  /-- The quotient orbicurve C_F. -/
  cF : Iut.HyperbolicOrbicurve (S1732A l).F
  cF_signature : cF.signature = sourceTypeOneOnePlusMinus
  /-- The sign-invariant quotient morphism `X_F -> C_F`. -/
  quotient : Iut.OrbicurveSignInvariantMorphism action cF
  /-- The universal property of the quotient. -/
  quotientWitness : Iut.OrbicurveSignQuotientWitness action quotient

/-- The first field of the paper-faithful datum. -/
noncomputable def S1886PaperCF.toFirstField {l : PrimeGeFive}
    (Q : S1886PaperCF l) : S1881CF l :=
  ⟨Q.cF, Q.cF_signature⟩

@[simp] theorem S1886PaperCF.toFirstField_val {l : PrimeGeFive}
    (Q : S1886PaperCF l) : (Q.toFirstField).1 = Q.cF := rfl

/-- The paper-faithful first missing datum supplies the literal first field. -/
theorem S1886PaperCF_firstField {l : PrimeGeFive} (Q : S1886PaperCF l) :
    Nonempty (S1881CF l) :=
  ⟨Q.toFirstField⟩

/-- The paper-faithful first missing datum contains the geometric `[-1]`
endomorphism. -/
theorem S1886PaperCF_involution {l : PrimeGeFive} (Q : S1886PaperCF l) :
    Nonempty (S1886EllipticInvolutionMissing l) :=
  ⟨Q.action.inversion⟩

/-- The exact first missing proposition of the D9 orbicurve over the actual
line: the paper-faithful sign quotient of the actual S1726 orbicurve. -/
def S1886FirstMissing (l : PrimeGeFive) : Prop :=
  Nonempty (S1886PaperCF l)

/-- The second missing datum, given the first field: the K-core scalar
extension. -/
def S1886SecondMissing {l : PrimeGeFive} (C : S1881CF l) : Prop :=
  Nonempty (S1886KCore l C)

/-- The third missing datum, given the K-core: X_K with its finite-etale cover
and group data. -/
def S1886ThirdMissing {l : PrimeGeFive} (C : S1881CF l)
    (K : S1886KCore l C) : Prop :=
  Nonempty (S1886XKCoverData l C K)

/-- The first missing datum implies the literal first field. -/
theorem S1886FirstMissing_firstField {l : PrimeGeFive}
    (h : S1886FirstMissing l) : Nonempty (S1881CF l) :=
  h.elim S1886PaperCF_firstField

/-- The first missing datum implies the geometric involution. -/
theorem S1886FirstMissing_involution {l : PrimeGeFive}
    (h : S1886FirstMissing l) :
    Nonempty (S1886EllipticInvolutionMissing l) :=
  h.elim S1886PaperCF_involution

/-- The paper-faithful first datum plus the K-core and X_K/cover/groups data
fill the S1881 D9 orbicurve slot. -/
theorem S1886D9OrbicurveSlot_of_paperData {l : PrimeGeFive}
    (Q : S1886PaperCF l) (K : S1886KCore l Q.toFirstField)
    (D : S1886XKCoverData l Q.toFirstField K) :
    Nonempty (S1881D9OrbicurveSlot l) :=
  ⟨S1886D9OrbicurveSlotOfData Q.toFirstField K D⟩

/-- Every S1881 D9 orbicurve slot supplies the exact K-core datum of its
first field. -/
theorem S1886KCore_missing_of_slot {l : PrimeGeFive}
    (S : S1881D9OrbicurveSlot l) :
    S1886SecondMissing (S1886FirstFieldOfSlot S) :=
  ⟨S1886KCoreOfSlot S⟩

/-- Every S1881 D9 orbicurve slot supplies the exact X_K/cover/groups datum. -/
theorem S1886XKCoverData_missing_of_slot {l : PrimeGeFive}
    (S : S1881D9OrbicurveSlot l) :
    S1886ThirdMissing (S1886FirstFieldOfSlot S) (S1886KCoreOfSlot S) :=
  ⟨S1886XKCoverDataOfSlot S⟩

/-! ## 8. Why the literal first field is too weak: signature is metadata

`Iut.HyperbolicOrbicurve` stores the signature (and its hyperbolic
certificate) as metadata on the stack, while the stack itself is an etale
pseudofunctor.  The following object exhibits this: the actual S1726 fiber,
relabeled with the `(1,1)^pm` signature.  It inhabits the literal first
field but is **not** Definition 3.1(d)'s C_F and must not be used as the
slot's `cF`; it is recorded here to prove that the literal first-field type
is not the honest obstruction.  This is exactly the
`realizedHyperbolicOrbicurve` signature-insertion pattern that the
repository audit classifies as an honest gap, not as geometric realization. -/

/-- The actual S1726 fiber with the `(1,1)^pm` label inserted. -/
noncomputable def S1886CFMetadataRelabel (l : PrimeGeFive) : S1881CF l :=
  ⟨realizedHyperbolicOrbicurve (S1732A l).F S1726Orbicurve.stack.fiber
      S1726Orbicurve.stack.isStack sourceTypeOneOnePlusMinus
      sourceTypeOneOnePlusMinus_hyperbolic,
    realizedHyperbolicOrbicurve_signature (S1732A l).F
      S1726Orbicurve.stack.fiber S1726Orbicurve.stack.isStack
      sourceTypeOneOnePlusMinus sourceTypeOneOnePlusMinus_hyperbolic⟩

/-- The relabeled object has literally the S1726 fiber. -/
theorem S1886CFMetadataRelabel_fiber (l : PrimeGeFive) :
    (S1886CFMetadataRelabel l).1.stack.fiber = S1726Orbicurve.stack.fiber :=
  rfl

/-- The relabeled object advertises `(1,1)^pm`. -/
theorem S1886CFMetadataRelabel_signature (l : PrimeGeFive) :
    (S1886CFMetadataRelabel l).1.signature = sourceTypeOneOnePlusMinus :=
  rfl

/-- Relabeling changes the stored signature on the very same fiber, so the
signature is not determined by the fiber. -/
theorem S1886CFMetadataRelabel_stack_ne_s1726 (l : PrimeGeFive) :
    (S1886CFMetadataRelabel l).1.stack ≠ S1726Orbicurve.stack := by
  intro h
  have hsig := congrArg Iut.EtaleStackOverField.orbicurveSignature h
  rw [show (S1886CFMetadataRelabel l).1.stack.orbicurveSignature =
      some sourceTypeOneOnePlusMinus from rfl,
    S1726Orbicurve_stack_orbicurveSignature] at hsig
  exact S1881OncePunctured_ne_typeOneOnePlusMinus
    (Option.some.inj hsig).symm

/-- The literal first-field type is inhabited by signature relabeling of the
actual S1726 fiber.  Hence it is not the honest first missing; the honest
missing is `S1886PaperCF`. -/
theorem S1886FirstField_type_inhabited_by_metadata (l : PrimeGeFive) :
    Nonempty (S1881CF l) :=
  ⟨S1886CFMetadataRelabel l⟩

/-! ## 9. Axiom footprint -/

#print axioms S1886D9SlotEquiv
#print axioms S1886D9Slot_nonempty_iff
#print axioms S1886D9SlotTail.toKCore
#print axioms S1886D9SlotTail.toXKCoverData
#print axioms S1886D9SlotTail.ofKCoreData
#print axioms S1886D9SlotTail_nonempty_iff
#print axioms S1886D9OrbicurveSlot_nonempty_iff
#print axioms S1886D9OrbicurveSlotOfData
#print axioms S1886KCore_stack_ne
#print axioms S1886FirstField_genus
#print axioms S1886KCore_genus
#print axioms S1886KCore_signature_ne
#print axioms S1886XKCoverData_xK_genus
#print axioms S1886XKCoverData_xK_stack_ne
#print axioms S1886D9SlotTail_xK_ne_cK
#print axioms S1886FiniteEtaleCoverOfSlot
#print axioms S1886GroupDataOfSlot
#print axioms S1886ExactSequenceOfSlot
#print axioms S1886ProjectionSurjectiveOfSlot
#print axioms S1886FirstField_stack_ne_s1726
#print axioms S1886NoSlotWithS1726
#print axioms S1886Slot_cK_ne_s1726
#print axioms S1886Slot_xK_ne_s1726
#print axioms S1886PaperCF.toFirstField
#print axioms S1886PaperCF_firstField
#print axioms S1886PaperCF_involution
#print axioms S1886FirstMissing_firstField
#print axioms S1886FirstMissing_involution
#print axioms S1886D9OrbicurveSlot_of_paperData
#print axioms S1886KCore_missing_of_slot
#print axioms S1886XKCoverData_missing_of_slot
#print axioms S1886CFMetadataRelabel
#print axioms S1886CFMetadataRelabel_stack_ne_s1726
#print axioms S1886FirstField_type_inhabited_by_metadata

end LeanFormal.IUT.XiFPaper.S1886D9OrbicurveActual

end
