import tmp.sheaf.xif.paper.S1732SourceAssemblyActual
import tmp.sheaf.xif.paper.S1320SectionsCuspActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionRankOneQuotient

/-!
# S1881: the exact D9/D7b/D8 frontier over the actual S1732 F' line

This file attacks the three remaining fields of the S1732 five-input record
hI, G6, G7, cusp, D9.

* D9 orbicurve: the actual F'-line data does not contain the F-side quotient
  orbicurve C_F of type (1,1)^pm, hence no K-core C_K of type
  (1,l-tors)^pm, hence no X_K of type (1,l-tors).  The actual S1726
  orbicurve is the upstairs once-punctured (1,1) object and is proved not
  to be any of these three by signature.  The exact first field is C_F.
* D9 cusp: the exact first field TorsionQuotientBoundaryOrigin is
  decomposed into its rank-one quotient plus a boundary residual.  The
  rank-one quotient is constructed from the actual hI input; the residual
  is a geometric boundary cusp together with the origin map on the nonzero
  classes.
* D7b: the exact first field is the place-indexed curve-side local-group
  family; the decomposition of S1727 is reused verbatim over the actual line.
* D8: the paper-faithful cusp is a boundary cusp of the missing C_K; the
  current SourceCuspClause is only a real epsilon plus a tail, and is
  unconstrained by the contract.  A real cusp coordinate on the missing
  K-core cusp is the exact missing datum.

No True, PUnit, arbitrary group, arbitrary proposition, sorry, admit, or
new axiom is used to fill a field.  The missing objects are exposed as types
and structures.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1881D9D7bActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1727SectionsFPrimeActual
open LeanFormal.IUT.XiFPaper.S1731D9PartialActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1320SectionsCuspActual

variable (l : PrimeGeFive)

/-! ## 1. The actual S1732 input -/

/-- The actual arithmetic input of the S1732 line. -/
abbrev S1881A (l : PrimeGeFive) : InitialThetaArithmeticData.{0} l :=
  S1732A l

@[simp] theorem S1881A_F : (S1881A l).F = S1720Field := rfl

@[simp] theorem S1881A_K : (S1881A l).K = S1720Field := rfl

/-- On the S1732 line the base field and the K-field are the same field. -/
theorem S1881A_F_eq_K : (S1881A l).F = (S1881A l).K := rfl

@[simp] theorem S1881A_curve : (S1881A l).curve = S1720Curve := rfl

/-! ## 2. Signature arithmetic: the actual S1726 object is not a D9 object

The paper's D9 orbicurve is the K-core quotient C_K of type
(1,l-tors)^pm, with X_K of type (1,l-tors).  The F-side quotient C_F
has type (1,1)^pm.  All three signatures differ from the once-punctured
(1,1) signature of the actual S1726 orbicurve. -/

theorem S1881OncePunctured_ne_typeOneOnePlusMinus :
    Iut.OrbicurveSignature.oncePuncturedElliptic ≠ sourceTypeOneOnePlusMinus := by
  intro h
  have hp : Iut.OrbicurveSignature.oncePuncturedElliptic.punctures =
      sourceTypeOneOnePlusMinus.punctures :=
    congrArg Iut.OrbicurveSignature.punctures h
  simp [Iut.OrbicurveSignature.oncePuncturedElliptic,
    sourceTypeOneOnePlusMinus] at hp

theorem S1881OncePunctured_ne_typeOneLTorsionPlusMinus (l : PrimeGeFive) :
    Iut.OrbicurveSignature.oncePuncturedElliptic ≠
      sourceTypeOneLTorsionPlusMinus l := by
  intro h
  have hp : Iut.OrbicurveSignature.oncePuncturedElliptic.punctures =
      (sourceTypeOneLTorsionPlusMinus l).punctures :=
    congrArg Iut.OrbicurveSignature.punctures h
  simp [Iut.OrbicurveSignature.oncePuncturedElliptic,
    sourceTypeOneLTorsionPlusMinus] at hp

theorem S1881OncePunctured_ne_typeOneLTorsion (l : PrimeGeFive) :
    Iut.OrbicurveSignature.oncePuncturedElliptic ≠ sourceTypeOneLTorsion l := by
  intro h
  have hp : Iut.OrbicurveSignature.oncePuncturedElliptic.punctures =
      (sourceTypeOneLTorsion l).punctures :=
    congrArg Iut.OrbicurveSignature.punctures h
  simp [Iut.OrbicurveSignature.oncePuncturedElliptic,
    sourceTypeOneLTorsion] at hp

theorem S1881TypeOneOnePlusMinus_ne_typeOneLTorsionPlusMinus
    (l : PrimeGeFive) :
    sourceTypeOneOnePlusMinus ≠ sourceTypeOneLTorsionPlusMinus l := by
  intro h
  have hlen : sourceTypeOneOnePlusMinus.stackyOrders.length =
      (sourceTypeOneLTorsionPlusMinus l).stackyOrders.length :=
    congrArg (fun s : Iut.OrbicurveSignature => s.stackyOrders.length) h
  simp [sourceTypeOneOnePlusMinus,
    sourceTypeOneLTorsionPlusMinus] at hlen

theorem S1881TypeOneOnePlusMinus_ne_typeOneLTorsion (l : PrimeGeFive) :
    sourceTypeOneOnePlusMinus ≠ sourceTypeOneLTorsion l := by
  intro h
  have hmem : (2 : Nat) ∈ sourceTypeOneOnePlusMinus.stackyOrders := by
    simp [sourceTypeOneOnePlusMinus]
  rw [congrArg Iut.OrbicurveSignature.stackyOrders h] at hmem
  simp [sourceTypeOneLTorsion] at hmem
  have hfive := l.ge_five
  omega

theorem S1881TypeOneLTorsion_ne_typeOneLTorsionPlusMinus
    (l : PrimeGeFive) :
    sourceTypeOneLTorsion l ≠ sourceTypeOneLTorsionPlusMinus l := by
  intro h
  have hlen : (sourceTypeOneLTorsion l).stackyOrders.length =
      (sourceTypeOneLTorsionPlusMinus l).stackyOrders.length :=
    congrArg (fun s : Iut.OrbicurveSignature => s.stackyOrders.length) h
  simp [sourceTypeOneLTorsion, sourceTypeOneLTorsionPlusMinus] at hlen

/-- The actual S1726 orbicurve is not the F-side quotient C_F. -/
theorem S1881S1726_not_CF :
    S1726Orbicurve.signature ≠ sourceTypeOneOnePlusMinus := by
  rw [S1726Orbicurve_signature]
  exact S1881OncePunctured_ne_typeOneOnePlusMinus

/-- The actual S1726 orbicurve is not the K-side quotient C_K. -/
theorem S1881S1726_not_CK (l : PrimeGeFive) :
    S1726Orbicurve.signature ≠ sourceTypeOneLTorsionPlusMinus l := by
  rw [S1726Orbicurve_signature]
  exact S1881OncePunctured_ne_typeOneLTorsionPlusMinus l

/-- The actual S1726 orbicurve is not the l-torsion cover X_K. -/
theorem S1881S1726_not_XK (l : PrimeGeFive) :
    S1726Orbicurve.signature ≠ sourceTypeOneLTorsion l := by
  rw [S1726Orbicurve_signature]
  exact S1881OncePunctured_ne_typeOneLTorsion l

/-! ## 3. The exact D9 orbicurve first field and slot -/

/-- Exact first field of the D9 orbicurve slot over the actual line: the
F-side quotient orbicurve C_F of paper type (1,1)^pm. -/
abbrev S1881CF (l : PrimeGeFive) : Type 1 :=
  { C : Iut.HyperbolicOrbicurve (S1732A l).F //
    C.signature = sourceTypeOneOnePlusMinus }

/-- The exact paper object of Definition 3.1(d) over the actual line: the
F-side quotient, its K-core scalar extension, the K-side (1,l-tors)^pm
quotient, the (1,l-tors) cover, and certified orbifold fundamental-group
data.  This is a structure, not an opaque (Prop, proof) pair. -/
structure S1881D9OrbicurveSlot (l : PrimeGeFive) where
  /-- The F-side quotient C_F, of type (1,1)^pm. -/
  cF : Iut.HyperbolicOrbicurve (S1732A l).F
  cF_signature : cF.signature = sourceTypeOneOnePlusMinus
  /-- The K-core scalar extension of C_F. -/
  core : SourceOrbicurveScalarExtension (S1732A l).F (S1732A l).K cF
  /-- The K-side quotient C_K, of type (1,l-tors)^pm. -/
  cK : Iut.HyperbolicOrbicurve (S1732A l).K
  cK_eq : cK = core.result
  cK_signature : cK.signature = sourceTypeOneLTorsionPlusMinus l
  /-- The l-torsion cover X_K, of type (1,l-tors). -/
  xK : Iut.HyperbolicOrbicurve (S1732A l).K
  xK_signature : xK.signature = sourceTypeOneLTorsion l
  /-- The natural finite-etale cover X_K -> C_K. -/
  coverMap : xK.Hom cK
  coverFiniteEtale : Iut.EtaleStackFiniteEtaleMorphism coverMap
  /-- Certified orbifold fundamental-group data of X_K. -/
  groups : Iut.OrbicurveFundamentalGroupData xK
    (Iut.AbsoluteGaloisProfinite (S1732A l).K)

/-- The first field of the D9 orbicurve slot. -/
def S1881D9OrbicurveSlot.firstField (S : S1881D9OrbicurveSlot l) :
    S1881CF l :=
  ⟨S.cF, S.cF_signature⟩

/-- The three signatures of the slot are pairwise distinct, so C_F, C_K,
and X_K are genuinely different objects even though F = K on the actual
line. -/
theorem S1881D9OrbicurveSlot.cF_ne_cK (S : S1881D9OrbicurveSlot l) :
    (S.cF : Iut.HyperbolicOrbicurve (S1732A l).K) ≠ S.cK := by
  intro h
  have hs : S.cF.signature = S.cK.signature := congrArg _ h
  exact S1881TypeOneOnePlusMinus_ne_typeOneLTorsionPlusMinus l
    (S.cF_signature.symm.trans (hs.trans S.cK_signature))

theorem S1881D9OrbicurveSlot.cF_ne_xK (S : S1881D9OrbicurveSlot l) :
    (S.cF : Iut.HyperbolicOrbicurve (S1732A l).K) ≠ S.xK := by
  intro h
  have hs : S.cF.signature = S.xK.signature := congrArg _ h
  exact S1881TypeOneOnePlusMinus_ne_typeOneLTorsion l
    (S.cF_signature.symm.trans (hs.trans S.xK_signature))

theorem S1881D9OrbicurveSlot.cK_ne_xK (S : S1881D9OrbicurveSlot l) :
    S.cK ≠ S.xK := by
  intro h
  have hs : S.cK.signature = S.xK.signature := congrArg _ h
  exact (S1881TypeOneLTorsion_ne_typeOneLTorsionPlusMinus l)
    (S.cK_signature.symm.trans (hs.trans S.xK_signature)).symm

/-- The D9 orbicurve missing statement: existence of the exact paper slot. -/
def S1881D9OrbicurveMissing (l : PrimeGeFive) : Prop :=
  Nonempty (S1881D9OrbicurveSlot l)

/-- An inhabitant of the exact slot gives the D9 orbicurve (Prop, proof)
pair with the slot-existence proposition as content. -/
def S1881D9OrbicurvePairOfSlot (S : S1881D9OrbicurveSlot l) :
    S1731D9OrbicurvePair l where
  prop := S1881D9OrbicurveMissing l
  proof := ⟨S⟩

@[simp] theorem S1881D9OrbicurvePairOfSlot_prop
    (S : S1881D9OrbicurveSlot l) :
    (S1881D9OrbicurvePairOfSlot l S).prop = S1881D9OrbicurveMissing l := rfl

/-! ## 4. The D9 cusp pair: actual rank-one quotient, exact boundary residual

hI supplies the rank-two torsion basis of E'.  Hence the rank-one
quotient Q of Definition 3.1(c) is actual.  The only remaining cusp data is
a boundary cusp of the K-side orbicurve together with the origin map on the
nonzero quotient classes. -/

/-- The actual rank-one quotient of the D9 cusp slot, constructed from the
large-image input hI (which contains the rank-two torsion basis). -/
noncomputable def S1881ActualRankOneQuotient (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    TorsionRankOneQuotientData l
      ((S1732A l).curve.baseChange (S1732A l).K) :=
  { torsion_basis := (S1725ImageContainsSL2_basis l hI).some }

/-- The actual rank-one quotient exists unconditionally from hI. -/
theorem S1881ActualRankOneQuotient_nonempty (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    Nonempty (TorsionRankOneQuotientData l
      ((S1732A l).curve.baseChange (S1732A l).K)) :=
  ⟨S1881ActualRankOneQuotient l hI⟩

/-- The actual quotient is rank one. -/
theorem S1881ActualRankOneQuotient_rank_one (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    Nonempty ((S1881ActualRankOneQuotient l hI).Quotient ≃ₗ[ZMod l.value]
      ZMod l.value) :=
  (S1881ActualRankOneQuotient l hI).quotient_is_rank_one

/-- The distinguished class of the actual quotient is nonzero. -/
theorem S1881ActualRankOneQuotient_distinguished_nonzero
    (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    (S1881ActualRankOneQuotient l hI).distinguishedClass ≠ 0 :=
  (S1881ActualRankOneQuotient l hI).distinguishedClass_nonzero

/-- The exact boundary residual of the D9 cusp origin at a fixed actual
rank-one quotient and a fixed K-side orbicurve. -/
structure S1881CuspBoundaryResidual (l : PrimeGeFive)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (Q : TorsionRankOneQuotientData l
      ((S1732A l).curve.baseChange (S1732A l).K)) where
  /-- The origin map on nonzero quotient classes. -/
  originMap : {q : Q.Quotient // q ≠ 0} → Iut.OrbicurveBoundaryCusp X
  /-- The selected boundary cusp. -/
  cusp : Iut.OrbicurveBoundaryCusp X
  /-- The distinguished class maps to the selected cusp. -/
  originMap_distinguishedClass :
    originMap ⟨Q.distinguishedClass, Q.distinguishedClass_nonzero⟩ = cusp

/-- The distinguished-class origin equation of a boundary residual. -/
theorem S1881CuspBoundaryResidual.originMap_distinguished
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    {Q : TorsionRankOneQuotientData l
      ((S1732A l).curve.baseChange (S1732A l).K)}
    (R : S1881CuspBoundaryResidual l (X := X) Q) :
    R.originMap ⟨Q.distinguishedClass, Q.distinguishedClass_nonzero⟩ =
      R.cusp :=
  R.originMap_distinguishedClass

/-- Exact decomposition of the D9 cusp origin: a rank-one quotient together
with its boundary residual.  No origin map or cusp is manufactured. -/
noncomputable def S1881CuspOriginEquiv (l : PrimeGeFive)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K} :
    TorsionQuotientBoundaryOrigin l (S1732A l) X ≃
      Σ Q : TorsionRankOneQuotientData l
          ((S1732A l).curve.baseChange (S1732A l).K),
        S1881CuspBoundaryResidual l (X := X) Q where
  toFun O :=
    ⟨O.rank_one_quotient,
      { originMap := O.originMap
        cusp := O.cusp
        originMap_distinguishedClass := O.originMap_distinguishedClass }⟩
  invFun p :=
    { rank_one_quotient := p.1
      originMap := p.2.originMap
      cusp := p.2.cusp
      originMap_distinguishedClass := p.2.originMap_distinguishedClass }
  left_inv O := by cases O; rfl
  right_inv p := by rcases p with ⟨Q, r⟩; cases r; rfl

/-- Nonemptiness of the D9 cusp origin is exactly: some rank-one quotient
carries a boundary residual. -/
theorem S1881CuspOrigin_nonempty_iff (l : PrimeGeFive)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K} :
    Nonempty (TorsionQuotientBoundaryOrigin l (S1732A l) X) ↔
      ∃ Q : TorsionRankOneQuotientData l
          ((S1732A l).curve.baseChange (S1732A l).K),
        Nonempty (S1881CuspBoundaryResidual l (X := X) Q) := by
  constructor
  · rintro ⟨O⟩
    exact ⟨O.rank_one_quotient, ⟨(S1881CuspOriginEquiv l O).2⟩⟩
  · rintro ⟨Q, ⟨R⟩⟩
    exact ⟨(S1881CuspOriginEquiv l).symm ⟨Q, R⟩⟩

/-- With the actual quotient fixed, a boundary residual fills the D9 cusp
origin. -/
theorem S1881CuspOrigin_of_actualResidual (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (R : S1881CuspBoundaryResidual l (X := X)
      (S1881ActualRankOneQuotient l hI)) :
    Nonempty (TorsionQuotientBoundaryOrigin l (S1732A l) X) :=
  ⟨(S1881CuspOriginEquiv l).symm ⟨_, R⟩⟩

/-- The D9 cusp (Prop, proof) pair from an actual boundary origin. -/
noncomputable def S1881D9CuspPairOfOrigin (l : PrimeGeFive)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (O : TorsionQuotientBoundaryOrigin l (S1732A l) X) :
    S1731D9CuspPair l where
  prop := ArithmeticCuspOriginCompatibility O
  proof := arithmeticCuspOriginCompatibility_of_supply O

@[simp] theorem S1881D9CuspPairOfOrigin_prop (l : PrimeGeFive)
    {X : Iut.HyperbolicOrbicurve (S1732A l).K}
    (O : TorsionQuotientBoundaryOrigin l (S1732A l) X) :
    (S1881D9CuspPairOfOrigin l O).prop =
      ArithmeticCuspOriginCompatibility O := rfl

/-- The exact missing part of the D9 cusp pair at a fixed D9 orbicurve slot:
a rank-one quotient with a boundary residual on C_K. -/
def S1881D9CuspMissing (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) : Prop :=
  ∃ Q : TorsionRankOneQuotientData l
      ((S1732A l).curve.baseChange (S1732A l).K),
    Nonempty (S1881CuspBoundaryResidual l (X := S.cK) Q)

/-- A boundary residual at the actual rank-one quotient witnesses the
missing statement at the slot. -/
theorem S1881D9CuspMissing_of_actualResidual (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (S : S1881D9OrbicurveSlot l)
    (R : S1881CuspBoundaryResidual l (X := S.cK)
      (S1881ActualRankOneQuotient l hI)) :
    S1881D9CuspMissing l S :=
  ⟨_, ⟨R⟩⟩

/-- The missing statement is exactly nonemptiness of the D9 cusp origin over
the slot's C_K. -/
theorem S1881D9CuspMissing_iff (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) :
    S1881D9CuspMissing l S ↔
      Nonempty (TorsionQuotientBoundaryOrigin l (S1732A l) S.cK) :=
  (S1881CuspOrigin_nonempty_iff (l := l) (X := S.cK)).symm

/-! ## 5. The full D9 record and the S1732 assembly

Once the exact D9 orbicurve slot and the D9 cusp origin are supplied, the two
missing D9 pairs are actual, and the S1732 assembly consumes them exactly as
before.  This isolates the two genuine geometric inputs of the D9 slot. -/

/-- The two missing D9 pairs, constructed from the exact orbicurve slot and
the exact cusp origin. -/
noncomputable def S1881D9MissingOfData (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l)
    (O : TorsionQuotientBoundaryOrigin l (S1732A l) S.cK) :
    S1731D9Missing l where
  orbicurve := S1881D9OrbicurvePairOfSlot l S
  cusp := S1881D9CuspPairOfOrigin l O

/-- The completed D9 supply over the actual S1730 selection, conditional
exactly on hI, the D9 orbicurve slot, and the D9 cusp origin. -/
noncomputable def S1881D9Supply (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (S : S1881D9OrbicurveSlot l)
    (O : TorsionQuotientBoundaryOrigin l (S1732A l) S.cK) :
    D9CompatibilitySupply :=
  S1732D9Supply l hI (S1881D9MissingOfData l S O)

@[simp] theorem S1881D9Supply_orbicurve (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (S : S1881D9OrbicurveSlot l)
    (O : TorsionQuotientBoundaryOrigin l (S1732A l) S.cK) :
    (S1881D9Supply l hI S O).orbicurve = S1881D9OrbicurveMissing l := rfl

@[simp] theorem S1881D9Supply_cusp (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) (S : S1881D9OrbicurveSlot l)
    (O : TorsionQuotientBoundaryOrigin l (S1732A l) S.cK) :
    (S1881D9Supply l hI S O).cusp =
      ArithmeticCuspOriginCompatibility O := rfl

/-- The S1732 source contract, with the D9 input replaced by the exact D9
orbicurve slot and cusp origin.  The remaining three inputs G6, G7,
Sc are the same as in S1732. -/
noncomputable def S1881S1732SourceData (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input)
    (G7 : S1732D7Input l)
    (Sc : SourceCuspClause)
    (S : S1881D9OrbicurveSlot l)
    (O : TorsionQuotientBoundaryOrigin l (S1732A l) S.cK) :
    SourceDefinition31Data.{0} l :=
  S1732SourceData l hI G6 G7 Sc (S1881D9MissingOfData l S O)

/-- The assembled contract's D9 orbicurve slot is the exact slot-existence
proposition. -/
@[simp] theorem S1881S1732SourceData_orbicurve (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input) (G7 : S1732D7Input l)
    (Sc : SourceCuspClause) (S : S1881D9OrbicurveSlot l)
    (O : TorsionQuotientBoundaryOrigin l (S1732A l) S.cK) :
    (S1881S1732SourceData l hI G6 G7 Sc S O).arithmetic_orbicurve_compatibility =
      S1881D9OrbicurveMissing l := rfl

/-- The assembled contract's D9 cusp slot is the concrete global-origin
proposition. -/
@[simp] theorem S1881S1732SourceData_cusp (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l)
    (G6 : S1732D6Input) (G7 : S1732D7Input l)
    (Sc : SourceCuspClause) (S : S1881D9OrbicurveSlot l)
    (O : TorsionQuotientBoundaryOrigin l (S1732A l) S.cK) :
    (S1881S1732SourceData l hI G6 G7 Sc S O).arithmetic_cusp_compatibility =
      ArithmeticCuspOriginCompatibility O := rfl

/-! ## 6. D7b: the exact first field over the actual line

The S1732 D7 input is definitionally the S1727 D7b supply over the canonical
place-section layer.  Its first field is the place-indexed curve-side local
group family; the exact first-field/tail decomposition of S1727 is reused. -/

/-- The exact D7b input of S1732. -/
abbrev S1881D7bSupply (l : PrimeGeFive) : Type 1 :=
  S1732D7Input l

/-- The D7b input is definitionally the S1727 D7b supply. -/
theorem S1881D7bSupply_eq (l : PrimeGeFive) :
    S1881D7bSupply l = S1727SectionFirstMissing l := rfl

/-- The exact first field of D7b: the place-indexed curve-side local-group
family, not an arithmetic local Galois group. -/
abbrev S1881D7bFirstField (l : PrimeGeFive) : Type 1 :=
  S1727D7FirstField l

/-- The first field of any D7b supply. -/
def S1881D7bFirstFieldOfSupply (G : S1881D7bSupply l) :
    S1881D7bFirstField l :=
  G.localGroupCarrier

/-- Every D7b supply determines its first field. -/
theorem S1881D7bFirstField_needed (G : S1881D7bSupply l) :
    Nonempty (S1881D7bFirstField l) :=
  ⟨S1881D7bFirstFieldOfSupply l G⟩

/-- Exact D7b decomposition: first field plus tail. -/
theorem S1881D7b_nonempty_iff_firstField_tail (l : PrimeGeFive) :
    Nonempty (S1881D7bSupply l) ↔
      ∃ G0 : S1881D7bFirstField l,
        Nonempty (S1727D7Tail l G0) :=
  S1727SectionFirstMissing_nonempty_iff_firstField_tail l

/-- The canonical-layer slice of section clauses is exactly the D7b supply:
the actual arithmetic input determines the six D7a fields and nothing more. -/
theorem S1881D7b_canonicalFiber_nonempty_iff (l : PrimeGeFive) :
    Nonempty (S1727CanonicalFiber l) ↔ Nonempty (S1881D7bSupply l) :=
  S1727CanonicalFiber_nonempty_iff l

/-- The upstairs D7b carrier is the selected-place subtype of the actual F'. -/
theorem S1881D7b_valuationCarrier :
    (S1727Layer l).valuationCarrier =
      {v : NumberFieldPlace (S1732A l).K //
        v ∈ (SourceArithmeticPrelude.canonical (S1732A l)).selectedPlaces} := rfl

/-- The downstairs D7b carrier is the actual place carrier of the modification
field Q. -/
theorem S1881D7b_modifiedValuationCarrier :
    (S1727Layer l).modifiedValuationCarrier = NumberFieldPlace ℚ := rfl

/-! ## 7. D8: the real cusp coordinate over the missing K-core cusp

The paper's cusp is a boundary cusp of C_K; the current SourceCuspClause
is a real epsilon plus a tail.  The exact faithful D8 datum is a real
coordinate map on the missing K-core cusp. -/

/-- The faithful paper cusp of the D9 slot: a boundary cusp of C_K. -/
abbrev S1881PaperCusp (l : PrimeGeFive) (S : S1881D9OrbicurveSlot l) :
    Type 1 :=
  Iut.OrbicurveBoundaryCusp S.cK

/-- A real cusp coordinate on the missing K-core cusp, with positivity,
nonzeroness, a positive scale, and a proved compatibility proposition. -/
structure S1881RealCuspCoordinate (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) where
  epsilonOf : S1881PaperCusp l S → Real
  epsilon_positive : ∀ c, 0 < epsilonOf c
  epsilon_nonzero : ∀ c, epsilonOf c ≠ 0
  cuspScaleOf : S1881PaperCusp l S → Real
  cuspScale_positive : ∀ c, 0 < cuspScaleOf c
  epsilon_scale_relation : ∀ c, epsilonOf c * cuspScaleOf c ≠ 0
  epsilon_compatibility : S1881PaperCusp l S → Prop
  epsilon_compatibility_proved : ∀ c, epsilon_compatibility c

/-- The conditional SourceCuspClause from a real cusp coordinate and a
chosen paper cusp.  The real first field is the coordinate value, never an
arbitrary constant. -/
noncomputable def S1881CuspClauseOfCoordinate (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (R : S1881RealCuspCoordinate l S)
    (c : S1881PaperCusp l S) : SourceCuspClause where
  epsilon := R.epsilonOf c
  epsilon_positive := R.epsilon_positive c
  epsilon_nonzero := R.epsilon_nonzero c
  epsilon_compatibility := R.epsilon_compatibility c
  epsilon_compatibility_proved := R.epsilon_compatibility_proved c
  cuspScale := R.cuspScaleOf c
  cuspScale_positive := R.cuspScale_positive c
  epsilon_scale_relation := R.epsilon_scale_relation c

@[simp] theorem S1881CuspClauseOfCoordinate_epsilon (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (R : S1881RealCuspCoordinate l S)
    (c : S1881PaperCusp l S) :
    (S1881CuspClauseOfCoordinate l S R c).epsilon = R.epsilonOf c := rfl

/-- The current cusp contract is exactly a real first field plus a tail. -/
theorem S1881CuspClause_nonempty_iff_firstField_tail :
    Nonempty SourceCuspClause ↔
      ∃ e : S1320CuspFirstField, Nonempty (S1320CuspTail e) :=
  S1320CuspClause_nonempty_iff_firstField_tail

/-- The exact D8 missing object over the D9 slot: a real cusp coordinate on
the K-core cusp. -/
def S1881D8Missing (l : PrimeGeFive) (S : S1881D9OrbicurveSlot l) : Prop :=
  Nonempty (S1881RealCuspCoordinate l S)

/-! ## 8. Axiom footprint -/

#print axioms S1881S1726_not_CF
#print axioms S1881S1726_not_CK
#print axioms S1881S1726_not_XK
#print axioms S1881D9OrbicurveSlot.cF_ne_cK
#print axioms S1881D9OrbicurveSlot.cF_ne_xK
#print axioms S1881D9OrbicurveSlot.cK_ne_xK
#print axioms S1881D9OrbicurvePairOfSlot
#print axioms S1881ActualRankOneQuotient
#print axioms S1881ActualRankOneQuotient_nonempty
#print axioms S1881ActualRankOneQuotient_rank_one
#print axioms S1881ActualRankOneQuotient_distinguished_nonzero
#print axioms S1881CuspOriginEquiv
#print axioms S1881CuspOrigin_nonempty_iff
#print axioms S1881CuspOrigin_of_actualResidual
#print axioms S1881D9CuspPairOfOrigin
#print axioms S1881D9CuspMissing_of_actualResidual
#print axioms S1881D9MissingOfData
#print axioms S1881D9Supply
#print axioms S1881S1732SourceData
#print axioms S1881S1732SourceData_orbicurve
#print axioms S1881S1732SourceData_cusp
#print axioms S1881D7b_nonempty_iff_firstField_tail
#print axioms S1881D7b_canonicalFiber_nonempty_iff
#print axioms S1881CuspClauseOfCoordinate
#print axioms S1881CuspClause_nonempty_iff_firstField_tail

end LeanFormal.IUT.XiFPaper.S1881D9D7bActual

end
