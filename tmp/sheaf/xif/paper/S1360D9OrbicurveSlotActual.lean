import tmp.sheaf.xif.paper.S1319OrbicurveClauseActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility
import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31OrbicurveInstance

/-!
# S1360: D9 orbicurve slot — actual coarse quotient / exact X at K

The D9 orbicurve slot consumes an actual hyperbolic orbicurve over
K = (S1280Arithmetic l).K together with the K-core identification of
Definition 3.1(d).  S1319 supplies the actual coarse quotient
X_K/(+-1) at the point/clause level, and Example36 supplies the actual
punctured elliptic curve, the -1 involution and its geometric carrier.
Neither supplies the etale stack/fiber object, so this file:

* reuses the actual S1319 coarse-quotient clause and records the exact
  once-punctured orbifold slot (S1360OrbicurveSlotAtK), which fills the
  S1319 S1319OrbifoldPiData gap;
* records the paper-faithful D9 first field separately: an actual
  X : Iut.HyperbolicOrbicurve K of signature (1, l-tors), not the
  once-punctured (1,1) S1319 signature.  These two signatures are proved
  different below;
* records the exact K-core identification as a structure with actual
  F-side objects, scalar extensions, equations and the finite-etale cover
  X -> C_K, and records the paper-consistent signature typing: X_F is
  once-punctured (1,1), X_K is (1,l-tors), and the K-core scalar extension
  preserves only the genus, so the old forced signature equality is
  refuted (S1370 records the fix);
* proves the terminal stack and the point-fiber surrogate cannot fill the
  nonterminal slot, and that a point fiber has no surjective realization
  of the actual Gaussian curve points.

No terminal object is used.  No inhabitant of the exact D9 stack slot is
asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1360D9OrbicurveSlotActual

universe u

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

/-! ## 1. Reused actual S1319 coarse quotient -/

/-- The S1319 coarse quotient is actual at the point/clause level. -/
theorem s1360S1319Coarse_actual (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).curve = S1319Curve l := rfl

/-- The exact orbifold-Pi gap recorded by S1319. -/
def s1360OrbifoldPiGap (l : PrimeGeFive) : Prop :=
  S1319OrbifoldPiGap l

/-! ## 2. Exact first field -/

/-- Exact first field of the D9 orbicurve slot: a hyperbolic orbicurve over
K, with no stack or signature surrogate substituted for it. -/
abbrev S1360OrbicurveFirstField (l : PrimeGeFive) : Type 1 :=
  Iut.HyperbolicOrbicurve (S1280Arithmetic l).K

/-! ## 3. The S1319 once-punctured orbifold slot -/

/-- The S1319 once-punctured orbifold slot over K.  X is the exact first
field; the remaining fields are the nonterminality certificate, the
once-punctured signature certificate, and the actual orbifold fundamental
group data.  No inhabitant is asserted. -/
structure S1360OrbicurveSlotAtK (l : PrimeGeFive) where
  X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K
  nonterminal : S1319NonterminalFiber X
  signature : X.signature = Iut.OrbicurveSignature.oncePuncturedElliptic
  groups : Iut.OrbicurveFundamentalGroupData X
    (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)

/-- The S1319 slot is exactly the S1319 orbifold-Pi datum. -/
noncomputable def S1360OrbicurveSlotAtK.toOrbifoldPiData
    {l : PrimeGeFive} (S : S1360OrbicurveSlotAtK l) :
    S1319OrbifoldPiData l where
  X := S.X
  nonterminal := S.nonterminal
  signature := S.signature
  groups := S.groups

/-- Consequently an inhabitant of the S1319 slot fills the S1319
orbifold-Pi gap. -/
theorem s1360OrbifoldPiGap_of_slot {l : PrimeGeFive}
    (S : S1360OrbicurveSlotAtK l) :
    S1319OrbifoldPiGap l :=
  ⟨S.toOrbifoldPiData⟩

/-- The first field of the S1319 slot is definitionally the exact first
field. -/
theorem S1360OrbicurveSlotAtK_firstField {l : PrimeGeFive}
    (S : S1360OrbicurveSlotAtK l) :
    (S.X : S1360OrbicurveFirstField l) = S.X := rfl

/-- Nonterminality in the S1319 sense is exactly non-point-fiberness. -/
theorem s1360Nonterminal_iff_not_pointFiber {F : Type} [Field F]
    (X : Iut.HyperbolicOrbicurve F) :
    S1319NonterminalFiber X ↔ ¬ IsPointFiber X.stack.fiber := by
  constructor
  · rintro ⟨U, hU⟩ h
    exact hU (h U)
  · intro h
    by_contra hn
    exact h (fun U => by
      by_contra hU
      exact hn ⟨U, hU⟩)

/-- The actual S1319 prefix of the D9 slot: X, nonterminality and the
once-punctured signature, without the orbifold group data. -/
structure S1360OrbicurvePrefixAtK (l : PrimeGeFive) where
  X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K
  nonterminal : S1319NonterminalFiber X
  signature : X.signature = Iut.OrbicurveSignature.oncePuncturedElliptic

/-- Conditional actual prefix from Example36's exact missing D6 geometric
realization.  No MissingD6GeometricRealization is constructed here; the
hypothesis is the exact open D6 input. -/
noncomputable def S1360OrbicurvePrefixOfMissingD6 (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1280Arithmetic l).K) :
    S1360OrbicurvePrefixAtK l where
  X := realizedHyperbolicOrbicurve (S1280Arithmetic l).K D.fiber D.isStack
    Iut.OrbicurveSignature.oncePuncturedElliptic
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic
  nonterminal := by
    rw [s1360Nonterminal_iff_not_pointFiber]
    simpa [realizedHyperbolicOrbicurve_stack_fiber] using D.nondegenerate
  signature := rfl

/-- A supplied D6 geometric realization inhabits the exact first field. -/
theorem s1360FirstField_of_missingD6 (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1280Arithmetic l).K) :
    Nonempty (S1360OrbicurveFirstField l) :=
  ⟨(S1360OrbicurvePrefixOfMissingD6 l D).X⟩

/-! ## 4. The paper-faithful D9 first field: type (1, l-tors) -/

/-- The paper-faithful D9 first field: an actual hyperbolic orbicurve over
K whose signature is (1, l-tors), not the once-punctured (1,1) signature of
S1319. -/
abbrev S1360PaperOrbicurveFirstField (l : PrimeGeFive) : Type 1 :=
  { X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K //
    X.signature = sourceTypeOneLTorsion l }

/-- The paper D9 orbicurve slot over K: type (1, l-tors), nonterminal,
with actual orbifold fundamental group data. -/
structure S1360PaperOrbicurveSlotAtK (l : PrimeGeFive) where
  X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K
  nonterminal : S1319NonterminalFiber X
  signature : X.signature = sourceTypeOneLTorsion l
  groups : Iut.OrbicurveFundamentalGroupData X
    (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)

/-- The once-punctured signature and the (1, l-tors) signature are
different: their puncture counts are 1 and 0. -/
theorem s1360OncePunctured_ne_sourceTypeOneLTorsion (l : PrimeGeFive) :
    Iut.OrbicurveSignature.oncePuncturedElliptic ≠ sourceTypeOneLTorsion l := by
  intro h
  have hp : Iut.OrbicurveSignature.oncePuncturedElliptic.punctures =
      (sourceTypeOneLTorsion l).punctures :=
    congrArg Iut.OrbicurveSignature.punctures h
  simp [Iut.OrbicurveSignature.oncePuncturedElliptic,
    sourceTypeOneLTorsion] at hp

/-- The S1319 once-punctured slot cannot be the paper (1, l-tors) D9
slot: its signature is proved different. -/
theorem S1360OrbicurveSlotAtK.signature_ne_paper {l : PrimeGeFive}
    (S : S1360OrbicurveSlotAtK l) :
    S.X.signature ≠ sourceTypeOneLTorsion l := by
  intro h
  exact s1360OncePunctured_ne_sourceTypeOneLTorsion l
    (S.signature.symm.trans h)

/-- The paper slot cannot be the S1319 once-punctured slot. -/
theorem S1360PaperOrbicurveSlotAtK.signature_ne_s1319 {l : PrimeGeFive}
    (S : S1360PaperOrbicurveSlotAtK l) :
    S.X.signature ≠ Iut.OrbicurveSignature.oncePuncturedElliptic := by
  intro h
  exact s1360OncePunctured_ne_sourceTypeOneLTorsion l
    (h.symm.trans S.signature)

/-! ## 5. The exact K-core identification -/

/-- The K-core base change of Definition 3.1(d): C_K is the K-core
scalar extension of an actual F-side C_F (genus-preserving; the l-tors
decoration is additional K-side structure) and carries the paper's
(1, l-tors)^+- signature. -/
structure S1360KCoreBaseChange (l : PrimeGeFive) where
  /-- The actual F-side quotient orbicurve C_F. -/
  cF : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F
  /-- The actual K-side quotient orbicurve C_K. -/
  cK : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K
  /-- The actual scalar extension of C_F to K. -/
  cKExtension :
    SourceOrbicurveScalarExtension (S1280Arithmetic l).F
      (S1280Arithmetic l).K cF
  /-- C_K is the extension result. -/
  cK_eq_extension : cK = cKExtension.result
  /-- C_K has the paper's (1, l-tors)^+- signature. -/
  cK_type : cK.signature = sourceTypeOneLTorsionPlusMinus l

/-- The exact K-core identification at a fixed K-side X: the
C_K = C_F x_F K base change plus the natural finite-etale cover
X -> C_K of Definition 3.1(d). -/
structure S1360KCoreIdentification (l : PrimeGeFive)
    (X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    extends S1360KCoreBaseChange l where
  /-- X has the paper's (1, l-tors) signature. -/
  x_type : X.signature = sourceTypeOneLTorsion l
  /-- The natural finite-etale cover X -> C_K. -/
  coverMap : X.Hom cK
  /-- The cover is representably finite etale. -/
  coverFiniteEtale : Iut.EtaleStackFiniteEtaleMorphism coverMap

/-! ## 5b. Consistent signature typing of the three D5-D9 records

The D5-D9 records are now consistent with the paper typing.  The scalar
extension is the K-core extension of Definition 3.1(d): it preserves the
genus of the coarse curve, while the K-side (1,l-tors) and (1,l-tors)^+-
decorations add l-torsion stacky structure.  Hence X_F stays once-punctured
(1,1), X_K is (1,l-tors), and the records *force* the two signatures to be
distinct; they no longer force them equal. -/

/-- Signature-level consistency of one source sign-quotient record: the
F-side (1,1) and K-side (1,l-tors) signatures share only the genus and are
distinct. -/
theorem s1360SignatureTyping_of_fields
    {l : PrimeGeFive}
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    {xF : Iut.HyperbolicOrbicurve F} {xK : Iut.HyperbolicOrbicurve K}
    {E : SourceOrbicurveScalarExtension F K xF}
    (hF : xF.signature = sourceTypeOneOne)
    (hK : xK.signature = sourceTypeOneLTorsion l)
    (hEq : xK = E.result) :
    xK.signature.genus = xF.signature.genus ∧
      xK.signature ≠ xF.signature := by
  constructor
  · calc
      xK.signature.genus = E.result.signature.genus := by rw [hEq]
      _ = xF.signature.genus := E.genus_preserved
  · intro h
    have hF' : xF.signature =
        Iut.OrbicurveSignature.oncePuncturedElliptic := by
      rw [hF]
      apply Iut.OrbicurveSignature.ext <;> rfl
    exact s1360OncePunctured_ne_sourceTypeOneLTorsion l
      (hK.symm.trans (h.trans hF')).symm

/-- The corrected geometric core is consistent: once-punctured (1,1) on
the F-side, (1,l-tors) on the K-side, common genus, distinct signatures. -/
theorem s1360SourceSignQuotientGeometricCore_signature_typing
    (l : PrimeGeFive)
    (G : SourceSignQuotientGeometricCore (S1280Arithmetic l)) :
    G.xF.signature = sourceTypeOneOne ∧
    G.xK.signature = sourceTypeOneLTorsion l ∧
    G.xK.signature.genus = G.xF.signature.genus ∧
    G.xK.signature ≠ G.xF.signature := by
  obtain ⟨hgenus, hne⟩ :=
    s1360SignatureTyping_of_fields (l := l)
      G.xF_geometry.signature G.xKType G.xK_eq_extension
  exact ⟨G.xF_geometry.signature, G.xKType, hgenus, hne⟩

/-- The corrected completion-level record has the same consistent typing. -/
theorem s1360SourceCompletionSignQuotient_signature_typing
    (l : PrimeGeFive)
    (C : SourceCompletionSignQuotient (S1280Arithmetic l)) :
    C.xF.signature = sourceTypeOneOne ∧
    C.xK.signature = sourceTypeOneLTorsion l ∧
    C.xK.signature.genus = C.xF.signature.genus ∧
    C.xK.signature ≠ C.xF.signature := by
  obtain ⟨hgenus, hne⟩ :=
    s1360SignatureTyping_of_fields (l := l)
      C.xF_geometry.signature C.xKType C.xK_eq_extension
  exact ⟨C.xF_geometry.signature, C.xKType, hgenus, hne⟩

/-- The corrected assembled D5-D9 record has the same consistent typing. -/
theorem s1360SourceSignQuotientData_signature_typing
    (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) :
    S.xF.signature = sourceTypeOneOne ∧
    S.xK.signature = sourceTypeOneLTorsion l ∧
    S.xK.signature.genus = S.xF.signature.genus ∧
    S.xK.signature ≠ S.xF.signature := by
  obtain ⟨hgenus, hne⟩ :=
    s1360SignatureTyping_of_fields (l := l)
      S.xF_geometry.signature S.xKType S.xK_eq_extension
  exact ⟨S.xF_geometry.signature, S.xKType, hgenus, hne⟩

/-- The exact D9 orbicurve slot: paper (1, l-tors) orbicurve plus the
K-core identification. -/
structure S1360D9OrbicurveSlot (l : PrimeGeFive) where
  orbicurve : S1360PaperOrbicurveSlotAtK l
  kCore : S1360KCoreIdentification l orbicurve.X

/-- The first field of the exact D9 slot. -/
abbrev S1360D9OrbicurveSlot.firstField {l : PrimeGeFive}
    (S : S1360D9OrbicurveSlot l) :
    S1360OrbicurveFirstField l :=
  S.orbicurve.X

/-- The paper signature of the exact D9 slot. -/
theorem S1360D9OrbicurveSlot.signature {l : PrimeGeFive}
    (S : S1360D9OrbicurveSlot l) :
    S.firstField.signature = sourceTypeOneLTorsion l :=
  S.orbicurve.signature

/-! ## 6. No terminal and no point-fiber substitute -/

/-- The terminal constant stack cannot be the carrier of any hyperbolic
orbicurve, hence cannot be the first field of the slot. -/
theorem s1360Terminal_not_slot_carrier {l : PrimeGeFive}
    (S : S1360OrbicurveSlotAtK l) :
    S.X.stack ≠
      Definition31OrbicurveInstance.terminalConstantEtaleStack
        (S1280Arithmetic l).K :=
  fun h =>
    Definition31OrbicurveInstance.terminalConstantEtaleStack_not_hyperbolicOrbicurve_carrier
      (S1280Arithmetic l).K S.X h

/-- The same exclusion for the paper D9 slot. -/
theorem s1360Terminal_not_paper_slot_carrier {l : PrimeGeFive}
    (S : S1360PaperOrbicurveSlotAtK l) :
    S.X.stack ≠
      Definition31OrbicurveInstance.terminalConstantEtaleStack
        (S1280Arithmetic l).K :=
  fun h =>
    Definition31OrbicurveInstance.terminalConstantEtaleStack_not_hyperbolicOrbicurve_carrier
      (S1280Arithmetic l).K S.X h

/-- A point fiber is not nonterminal in the S1319 sense. -/
theorem s1360PointFiber_not_nonterminal {F : Type} [Field F]
    {X : Iut.HyperbolicOrbicurve F}
    (h : IsPointFiber X.stack.fiber) :
    ¬ S1319NonterminalFiber X := by
  rintro ⟨U, hU⟩
  exact hU (h U)

/-- The Example36 degenerate point-fiber orbicurve fails the nonterminal
condition of the S1319 slot. -/
theorem s1360DegeneratePointFiber_not_nonterminal (l : PrimeGeFive) :
    ¬ S1319NonterminalFiber
      (degeneratePointFiberOrbicurve (S1280Arithmetic l).K) :=
  s1360PointFiber_not_nonterminal
    (degeneratePointFiberOrbicurve_isPointFiber (S1280Arithmetic l).K)

/-- A point fiber has no surjective realization of the actual Gaussian
curve's projective points, so it cannot be the geometric stack of the D9
orbicurve. -/
theorem s1360PointFiber_no_gaussianCurvePointRealization
    (l : PrimeGeFive)
    {fiber : Iut.EtaleStackPseudofunctor (S1280Arithmetic l).K}
    (h : IsPointFiber fiber) :
    ¬ ∃ f :
        fiber.obj
          (LocallyDiscrete.mk
            (Opposite.op (baseSchemeObject (S1280Arithmetic l).K))) →
          (S1280Arithmetic l).curve.curve.toProjective.Point,
        Function.Surjective f := by
  apply no_curvePointRealization_of_pointFiber (F := (S1280Arithmetic l).K)
    (curve := (S1280Arithmetic l).curve) h
  obtain ⟨x, y, hxy⟩ := S1319PuncturedPoints_nontrivial l
  exact ⟨x.1, y.1, fun hsub => hxy (Subtype.ext hsub)⟩

/-! ## 7. Axiom footprint -/

#print axioms s1360S1319Coarse_actual
#print axioms S1360OrbicurveSlotAtK.toOrbifoldPiData
#print axioms s1360OrbifoldPiGap_of_slot
#print axioms s1360Nonterminal_iff_not_pointFiber
#print axioms S1360OrbicurvePrefixOfMissingD6
#print axioms s1360FirstField_of_missingD6
#print axioms s1360OncePunctured_ne_sourceTypeOneLTorsion
#print axioms S1360OrbicurveSlotAtK.signature_ne_paper
#print axioms S1360KCoreBaseChange
#print axioms s1360SignatureTyping_of_fields
#print axioms s1360SourceSignQuotientGeometricCore_signature_typing
#print axioms s1360SourceCompletionSignQuotient_signature_typing
#print axioms s1360SourceSignQuotientData_signature_typing
#print axioms s1360Terminal_not_slot_carrier
#print axioms s1360PointFiber_not_nonterminal
#print axioms s1360DegeneratePointFiber_not_nonterminal
#print axioms s1360PointFiber_no_gaussianCurvePointRealization

end LeanFormal.IUT.XiFPaper.S1360D9OrbicurveSlotActual

end
