/-
  Instance-supply reduction for the etale-stack unit of Definition 3.1, and
  the precise source-binding card.

  Paper anchors (`D:\lean\papers\motizuki_corpus\text\Inter-universal
  Teichmuller Theory I.txt`):

  * Definition 3.1(b), extraction lines 3131-3157: `X_F` is a once-punctured
    elliptic curve over `F` and `X_F -> C_F` is the stack-theoretic quotient
    of `X_F` by its unique `F`-involution `-1`; the source object is an
    honest etale stack with geometric content, not a formal witness.
  * Definition 3.1(d), extraction lines 3185-3215: `C_K` of type
    `(1, l-tors)^+-` and `X_K` of type `(1, l-tors)` over `K`.

  Consumers of the unit (report section 22): `SourceHodgeTheaterBridge`;
  `SourceOriginalInput.lean:39-43` (`OriginalInput` takes
  `SourceDefinition31Data` and `SourceHodgeTheaterFamily`);
  `SourceH1H2Construction.lean:273-279` (`H1FamilyPackage`). None of them
  consumes a raw stack fiber, so none of them may gate on this file's
  existence theorem; they gate on the full geometric-core card below.

  What this file carries (reduction status):

  * Route A, proved: the constant pseudofunctor at the one-point category
    `SourceStackPointObj` is an honest stack for the big etale topology of
    `SchemeOverField F`, for every field `F`. The descent functors act
    between categories whose hom types are subsingletons and whose objects
    are all isomorphic, so `toDescentData` is an equivalence and Mathlib's
    `isStackFor_iff` closes `IsStackFor`. Consequently
    `EtaleStackInstanceSupply F`, the stack unit over both source fields of
    every arithmetic root, and `Nonempty (Iut.HyperbolicOrbicurve F)` are
    all inhabited.

    Degeneracy warning: this witness has no geometric content. Its fiber is
    a one-point category and the hyperbolic signature is inserted by
    `realizedHyperbolicOrbicurve`, not realized by the fiber. It discharges
    only the existence shape of the unit; it must not stand for the source
    orbicurve of Definition 3.1(b), and no downstream consumer may treat
    the corollaries below as source content.

  * Route B (scheme-representable fiber,
    `Iut.schemeRepresentableEtalePseudofunctor`) and Route C (discrete
    section/sheaf) were evaluated but not pushed to a proof: both would
    need heavier descent bookkeeping, and even then the signature is
    reinserted as metadata rather than realized, so neither would close the
    card below. The real construction belongs to the D6 line
    (`SourceDefinition31OrbicurveInstance`); no import of that line is
    taken here and no name is claimed on its behalf.

  * Source-binding card (open): of the 22 fields of
    `SourceSignQuotientGeometricCore`
    (`SourceSignQuotientConstruction.lean:30`), only the signature-shaped
    pair `xF`, `xF_geometry` is provided here. The involution and its
    uniqueness, the sign action with quotient and its witness, the two
    group-data records with the inclusion, the type equations `xKType`,
    `cKType`, the scalar extensions with their equations `xK_eq_extension`,
    `cK_eq_extension`, and the boundary cusp `epsilon` remain on the card.
    Additionally the current curve binding `SourceOncePuncturedGeometry` is
    equivalent to a bare signature equation (it never uses its `curve`
    argument); this is recorded below as
    `sourceOncePuncturedGeometry_nonempty_iff_signature` and is the formal
    reason the card needs strengthening before it can serve as a source
    binding.

  Boundaries: no `RootLemmas` import; the place-partition (D11-E) and
  D3/D4 lines are untouched; the two D3.1 contracts and the previously
  frozen reduction files are read-only here.
-/
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction

open CategoryTheory

namespace LeanFormal.IUT

universe u

/-! ## Route A: the one-point carrier -/

/-- The one-point carrier for the constant etale stack: the one-object
category used as the fiber of the constant pseudofunctor. -/
inductive SourceStackPointObj : Type u where
  | point : SourceStackPointObj

instance sourceStackPointObjSubsingleton : Subsingleton SourceStackPointObj where
  allEq a b := by cases a; cases b; rfl

instance sourceStackPointObjCategory : Category SourceStackPointObj where
  Hom _ _ := SourceStackPointObj
  id _ := SourceStackPointObj.point
  comp _ _ := SourceStackPointObj.point
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

instance sourceStackPointObjHomSubsingleton (X Y : SourceStackPointObj) :
    Subsingleton (X ⟶ Y) :=
  sourceStackPointObjSubsingleton

/-- The one-point category as an object of `Cat`. -/
abbrev sourceStackPointCarrier : Cat.{u, u} :=
  Cat.of SourceStackPointObj

/-- The constant functor from schemes over `F` to the one-point category. -/
noncomputable def sourceStackPointFiberFunctor (F : Type u) [Field F] :
    (Iut.SchemeOverField F)ᵒᵖ ⥤ Cat.{u, u} where
  obj _ := sourceStackPointCarrier
  map _ := 𝟙 sourceStackPointCarrier
  map_id _ := rfl
  map_comp _ _ := (Category.comp_id (𝟙 sourceStackPointCarrier)).symm

/-- The constant one-point-valued etale pseudofunctor over `F`. -/
noncomputable def sourceStackPointEtaleFiber (F : Type u) [Field F] :
    Iut.EtaleStackPseudofunctor F :=
  (sourceStackPointFiberFunctor F).toPseudofunctor'

/-! ## Route A: the descent functors are equivalences -/

/-- For the one-point fiber, `toDescentData` along the arrows of any
presieve is an equivalence: all hom types are subsingletons and all objects
are isomorphic, so faithfulness, fullness and essential surjectivity hold. -/
theorem isEquivalence_toDescentData_sourceStackPointEtaleFiber
    (F : Type u) [Field F]
    {S : Iut.SchemeOverField F} (R : Presieve S) :
    ((sourceStackPointEtaleFiber F).toDescentData
      (fun f : R.category => f.obj.hom)).IsEquivalence := by
  refine { faithful := ⟨fun {A B} φ ψ _ =>
            @Subsingleton.elim SourceStackPointObj sourceStackPointObjSubsingleton
              φ ψ⟩,
           full := ⟨fun {A B} c => ?_⟩,
           essSurj := ⟨fun Y => ?_⟩ }
  · refine ⟨eqToHom (@Subsingleton.elim SourceStackPointObj
        sourceStackPointObjSubsingleton A B), ?_⟩
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact @Subsingleton.elim SourceStackPointObj sourceStackPointObjSubsingleton _ _
  · refine ⟨SourceStackPointObj.point, ⟨?_⟩⟩
    refine Pseudofunctor.DescentData.isoMk
      (fun i => eqToIso (@Subsingleton.elim SourceStackPointObj
        sourceStackPointObjSubsingleton _ _)) ?_
    intros
    exact @Subsingleton.elim SourceStackPointObj sourceStackPointObjSubsingleton _ _

/-- `IsStackFor` at any presieve for the one-point fiber. -/
theorem sourceStackPointEtaleFiber_isStackFor (F : Type u) [Field F]
    {S : Iut.SchemeOverField F} (R : Presieve S) :
    (sourceStackPointEtaleFiber F).IsStackFor R :=
  (Pseudofunctor.isStackFor_iff (sourceStackPointEtaleFiber F) R).2
    (isEquivalence_toDescentData_sourceStackPointEtaleFiber F R)

/-- The one-point fiber is an etale stack over `F` for the big etale
topology. -/
theorem sourceStackPointEtaleFiber_isStack (F : Type u) [Field F] :
    (sourceStackPointEtaleFiber F).IsStack
      (Iut.SchemeOverField.etaleTopology F) := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro S R _
  exact sourceStackPointEtaleFiber_isStackFor F R.arrows

/-- Route A output: the etale-stack instance supply is inhabited for every
field. Degenerate witness -- see the module documentation. -/
theorem etaleStackInstanceSupply_sourceStackPoint (F : Type u) [Field F] :
    EtaleStackInstanceSupply F :=
  ⟨sourceStackPointEtaleFiber F, sourceStackPointEtaleFiber_isStack F⟩

/-- The stack unit over both source fields holds for every arithmetic root.
Degenerate witness: no geometric-core content is constructed. -/
theorem geometricCoreStackUnit_of_sourceStackPoint (l : PrimeGeFive) :
    GeometricCoreStackUnit.{u} l := by
  intro A
  exact ⟨etaleStackInstanceSupply_sourceStackPoint A.F,
    etaleStackInstanceSupply_sourceStackPoint A.K⟩

/-- The wrapper `HyperbolicOrbicurve F` is inhabited for every field.
Degenerate witness: the signature is inserted by
`realizedHyperbolicOrbicurve`, not realized by the fiber. -/
theorem nonempty_hyperbolicOrbicurve_of_sourceStackPoint (F : Type u)
    [Field F] :
    Nonempty (Iut.HyperbolicOrbicurve F) :=
  (nonempty_hyperbolicOrbicurve_iff_stackInstanceSupply F).2
    (etaleStackInstanceSupply_sourceStackPoint F)

/-! ## The vacuity of the current curve binding -/

/-- The current source binding over a curve is equivalent to a bare
signature equation: `SourceOncePuncturedGeometry` stores only
`X.signature = sourceTypeOneOne` and never uses its `curve` argument.
This is the precise reason the source-binding card must be strengthened
before it can serve as a binding. -/
theorem sourceOncePuncturedGeometry_nonempty_iff_signature
    {F : Type u} [Field F] (curve : PuncturedEllipticCurve F)
    (X : Iut.HyperbolicOrbicurve F) :
    Nonempty (InitialThetaSource.SourceOncePuncturedGeometry curve X) ↔
      X.signature = InitialThetaSource.sourceTypeOneOne :=
  ⟨fun h => h.some.signature, fun h => ⟨⟨h⟩⟩⟩

/-- The signature-shaped part of the geometric core is reachable from the
one-point fiber: the `xF` field and the whole current `xF_geometry`
certificate. Everything else in the 22-field core remains on the card. -/
theorem exists_sourceOncePuncturedGeometry_of_sourceStackPoint
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l) :
    ∃ XF : Iut.HyperbolicOrbicurve A.F,
      Nonempty (InitialThetaSource.SourceOncePuncturedGeometry A.curve XF) := by
  refine ⟨realizedHyperbolicOrbicurve A.F (sourceStackPointEtaleFiber A.F)
    (sourceStackPointEtaleFiber_isStack A.F)
    InitialThetaSource.sourceTypeOneOne
    InitialThetaSource.sourceTypeOneOne_hyperbolic, ?_⟩
  exact ⟨⟨rfl⟩⟩

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceEtaleStackInstanceSupplyReduction : Obligation :=
  { id := "IUT-I.definition-3.1-etale-stack-instance-supply-reduction"
    source :=
      "IUT I, Definition 3.1(b),(d); extraction lines 3131-3157, 3185-3215"
    status := VerificationStatus.interface
    note :=
      "Point-fiber reduction of `EtaleStackInstanceSupply` " ++
        "(SourceClauseAssemblyUnitsReduction.lean:379). Proved: the " ++
        "constant pseudofunctor at the one-point category is a stack for " ++
        "the big etale topology over every field (descent functors are " ++
        "equivalences by subsingleton homs and a single object), so the " ++
        "supply, the stack unit over both source fields and " ++
        "`Nonempty (HyperbolicOrbicurve F)` are inhabited. Degenerate " ++
        "witness: no geometric content; it discharges only the existence " ++
        "shape of the unit. The source-binding card (involution and " ++
        "uniqueness, sign action with quotient, group data, group " ++
        "inclusion, scalar extensions, type equations, boundary cusp) " ++
        "remains open, to be constructed by the D6 line " ++
        "(`SourceDefinition31OrbicurveInstance`, no import). The current " ++
        "curve binding `SourceOncePuncturedGeometry` is equivalent to a " ++
        "bare signature equation. Consumers must gate on the full card; " ++
        "consume-side anchors: `SourceHodgeTheaterBridge`, " ++
        "`SourceOriginalInput.lean:39-43`, " ++
        "`SourceH1H2Construction.lean:273-279`."
    dependsOn :=
      [ "IUT-I.definition-3.1-clause-assembly-units-reduction" ] }

end LeanFormal.IUT.Audit
