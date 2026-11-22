import tmp.sheaf.xif.paper.S1927GlobalFrobenioidLogShellActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceEvaluationUnitPortionConjugation

/-!
# S1951: the four source corners and the Kummer-evaluation square on S1895PaperO

The S1927 packet leaves the paper's four coric vertices env, gau, LGP, lgp and
their Kummer-evaluation square as parameters (S1927KummerEvaluationSquareActual).
This file constructs, on the actual S1895 paper input, the four actual source
F-prime-strips

  env = I.fPrimeStripAt 0 0,  gau = I.fPrimeStripAt 0 1,
  LGP = I.fPrimeStripAt 1 0,  lgp = I.fPrimeStripAt 1 1,

a common product group S1895KummerGroup I (the canonical product of the q-pilot
core strip), and actual factor maps from the common group to all four strips
through the actual source links I.fLinkAt.  On these data it constructs the
left/right Kummer arrows, the upper evaluation arrow, and the reduced
Kummer-evaluation square by the paper's conjugation instruction
(SourceKummerEvaluationSquare.ofThreeLegs).

The construction is actual at the reduced source-strip level: every strip
equivalence is an actual source link, and every Kummer isomorphism is the
actual strip-equivalence-induced TimesMuKummer.Isomorphism (Units.mapEquiv of
isoMon).  It does NOT assert that the four source strips are the paper's
F_env/F_gau/F_LGP/F_lgp; that is the missing definition R3 of
SourceKummerEvaluationArrows.  The first stateable reduced missing after the
square is the paper's operation-level Kummer/evaluation content on those
vertices, and the q-pilot anchor identification (R6); both are recorded as
missing definitions in section 5 and are not replaced by a fake type.

The S1927 interface fixes the production product-group topology instance
FPrimeStrip.productPiTopology (the fallback instance used by the existing
source interface); this file uses that instance.  The paper's profinite
topology is a separate missing datum and is not claimed here.

No forbidden placeholder, empty type, arbitrary inhabitant or assumption-only
Nonempty gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual

universe uV uG

/-! ## 1. The actual strip-equivalence Kummer isomorphism over a common group -/

namespace General

variable {V : Type uV} {G : Type uG} [Group G] [TopologicalSpace G]
variable {upper lower : FPrimeStrip V}

/-- The quotient of the units by torsion, transported by a multiplicative
equivalence of unit groups. -/
noncomputable def quotientUnitsEquiv {U W : Type*} [CommGroup U] [CommGroup W]
    (e : U ≃* W) : TimesMuQuotient U ≃* TimesMuQuotient W :=
  QuotientGroup.congr (CommGroup.torsion U) (CommGroup.torsion W) e e.map_torsion

@[simp] theorem quotientUnitsEquiv_quotientMap
    {U W : Type*} [CommGroup U] [CommGroup W] (e : U ≃* W) (u : U) :
    quotientUnitsEquiv e (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (e u) := rfl

/-- The actual quotient equivalence induced by a strip equivalence. -/
noncomputable def xMuQuotientEquiv (φ : FPrimeStripEquiv upper lower) (v : V) :
    TimesMuQuotient ((upper.Mon v)ˣ) ≃* TimesMuQuotient ((lower.Mon v)ˣ) :=
  quotientUnitsEquiv (Units.mapEquiv (φ.isoMon v))

/-- The lower factor map induced by a strip equivalence and a factor map to the
upper strip. -/
def factorLowerOfEquiv (φ : FPrimeStripEquiv upper lower)
    (factorUpper : ∀ v : V, G →* upper.toDPrimeStrip.Pi v) (v : V) :
    G →* lower.toDPrimeStrip.Pi v :=
  (φ.isoPi v).toMonoidHom.comp (factorUpper v)

/-- The actual Kummer isomorphism induced by a strip equivalence, on an
arbitrary common group acting through a supplied factor map to the upper
strip.  This is the strip-equivalence comparison, not the paper's operation-level
Kummer isomorphism. -/
noncomputable def kummerIsoOfFactors (φ : FPrimeStripEquiv upper lower)
    (factorUpper : ∀ v : V, G →* upper.toDPrimeStrip.Pi v) (v : V) :
    TimesMuKummer.Isomorphism
      ((upper.unitsAction v).comp (factorUpper v))
      ((lower.unitsAction v).comp (factorLowerOfEquiv φ factorUpper v)) where
  equiv := xMuQuotientEquiv φ v
  equivariant := by
    intro g x
    obtain ⟨u, rfl⟩ := TimesMuQuotient.quotientMap_surjective x
    change xMuQuotientEquiv φ v
        (TimesMuQuotient.quotientMap ((upper.unitsAction v) (factorUpper v g) u)) =
      TimesMuQuotient.quotientMap
        ((lower.unitsAction v) (φ.isoPi v (factorUpper v g))
          (Units.mapEquiv (φ.isoMon v) u))
    rw [xMuQuotientEquiv, quotientUnitsEquiv_quotientMap]
    congr 1
    ext
    simpa [FPrimeStrip.unitsAction_val] using
      φ.compatAction v (factorUpper v g) (u : upper.Mon v)
  invariantImage := by
    intro H
    let eU : (upper.Mon v)ˣ ≃* (lower.Mon v)ˣ := Units.mapEquiv (φ.isoMon v)
    have hfixed :
        eU '' (TimesMuKummer.fixedSubgroup
          ((upper.unitsAction v).comp (factorUpper v)) H :
          Set (upper.Mon v)ˣ) =
        (TimesMuKummer.fixedSubgroup
          ((lower.unitsAction v).comp (factorLowerOfEquiv φ factorUpper v)) H :
          Set (lower.Mon v)ˣ) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        intro g
        change (lower.unitsAction v)
          ((φ.isoPi v) ((factorUpper v) (g : G))) (eU u) = eU u
        conv_rhs => rw [← hu g]
        ext
        simpa [eU, FPrimeStrip.unitsAction_val, factorLowerOfEquiv,
          MonoidHom.comp_apply] using
          (φ.compatAction v ((factorUpper v) (g : G)) (u : upper.Mon v)).symm
      · intro hy
        refine ⟨eU.symm y, ?_, eU.apply_symm_apply y⟩
        intro g
        apply eU.injective
        rw [eU.apply_symm_apply]
        have h := hy g
        have h' : ((lower.action v)
            ((φ.isoPi v) ((factorUpper v) (g : G)))) (y : lower.Mon v) =
              (y : lower.Mon v) := by
          simpa [FPrimeStrip.unitsAction_val, factorLowerOfEquiv,
            MonoidHom.comp_apply] using congrArg Units.val h
        apply Units.ext
        have hc := φ.compatAction v ((factorUpper v) (g : G))
          ((eU.symm y : (upper.Mon v)ˣ) : upper.Mon v)
        dsimp [eU] at hc ⊢
        simpa [Units.coe_mapEquiv, FPrimeStrip.unitsAction_val, h'] using hc
    have hmap : ∀ u : (upper.Mon v)ˣ,
        quotientUnitsEquiv eU (TimesMuQuotient.quotientMap u) =
          TimesMuQuotient.quotientMap (eU u) := by
      intro u; exact quotientUnitsEquiv_quotientMap eU u
    change quotientUnitsEquiv eU ''
        (TimesMuKummer.invariantImage
          ((upper.unitsAction v).comp (factorUpper v)) H) =
      TimesMuKummer.invariantImage
        ((lower.unitsAction v).comp (factorLowerOfEquiv φ factorUpper v)) H
    rw [TimesMuKummer.invariantImage, TimesMuKummer.invariantImage]
    ext x
    constructor
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨eU u, hfixed ▸ ⟨u, hu, rfl⟩, hmap u⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨TimesMuQuotient.quotientMap (eU.symm u), ?_, ?_⟩
      · refine ⟨eU.symm u, ?_, rfl⟩
        have hpre : eU ⁻¹'
            (TimesMuKummer.fixedSubgroup
              ((lower.unitsAction v).comp
                (factorLowerOfEquiv φ factorUpper v)) H :
              Set (lower.Mon v)ˣ) =
            (TimesMuKummer.fixedSubgroup
              ((upper.unitsAction v).comp (factorUpper v)) H :
              Set (upper.Mon v)ˣ) := by
          rw [← hfixed, Set.preimage_image_eq _ eU.injective]
        rw [← hpre]
        simpa using hu
      · rw [hmap, eU.apply_symm_apply]

/-- The actual times-mu Kummer layer over the common group, induced by the
actual strip equivalence. -/
noncomputable def layerOfFactors (φ : FPrimeStripEquiv upper lower)
    (factorUpper : ∀ v : V, G →* upper.toDPrimeStrip.Pi v) :
    SourceTimesMuKummerLayer G upper lower where
  sourceAction := fun v => (upper.unitsAction v).comp (factorUpper v)
  targetAction := fun v =>
    (lower.unitsAction v).comp (factorLowerOfEquiv φ factorUpper v)
  kummer := fun v => kummerIsoOfFactors φ factorUpper v

/-- The actual evaluation unit portion over the common group, induced by the
actual strip equivalence. -/
noncomputable def unitPortionOfFactors (φ : FPrimeStripEquiv upper lower)
    (factorUpper : ∀ v : V, G →* upper.toDPrimeStrip.Pi v) :
    SourceEvaluationUnitPortion G upper lower :=
  SourceEvaluationUnitPortion.ofKummerLayer (layerOfFactors φ factorUpper)

end General

open General

/-! ## 2. The S1895 paper input, its four actual source strips, and the common group -/

/-- The place type of the S1895 paper input. -/
abbrev PaperV : Type := FinitePrimePlace 2 7

/-- The actual S1527 input carried by an S1895 paper input. -/
abbrev paperInput (D : S1895PaperInput) : OriginalInput D.l PaperV :=
  S1895PaperInput.I D

/-- The actual source F-prime-strip used for the paper's env corner. -/
abbrev envStrip (D : S1895PaperInput) : FPrimeStrip PaperV :=
  (paperInput D).fPrimeStripAt 0 0

/-- The actual source F-prime-strip used for the paper's gau corner. -/
abbrev gauStrip (D : S1895PaperInput) : FPrimeStrip PaperV :=
  (paperInput D).fPrimeStripAt 0 1

/-- The actual source F-prime-strip used for the paper's LGP corner. -/
abbrev lgpStrip (D : S1895PaperInput) : FPrimeStrip PaperV :=
  (paperInput D).fPrimeStripAt 1 0

/-- The actual source F-prime-strip used for the paper's lgp corner. -/
abbrev lgpLowerStrip (D : S1895PaperInput) : FPrimeStrip PaperV :=
  (paperInput D).fPrimeStripAt 1 1

/-- The common product group of the actual q-pilot core strip. -/
abbrev KummerGroup (D : S1895PaperInput) : Type :=
  S1895KummerGroup (paperInput D)

/-- The projection from the common group to the LGP (core) strip. -/
noncomputable def factorLGP (D : S1895PaperInput) (v : PaperV) :
    KummerGroup D →* (lgpStrip D).toDPrimeStrip.Pi v :=
  Pi.evalMonoidHom ((lgpStrip D).toDPrimeStrip.Pi) v

/-- The actual source link from the core strip to the env strip. -/
noncomputable def linkLGPToEnv (D : S1895PaperInput) :
    FPrimeStripEquiv (lgpStrip D) (envStrip D) :=
  (paperInput D).fLinkAt 1 0 0 0

/-- The actual source link from the core strip to the gau strip. -/
noncomputable def linkLGPToGau (D : S1895PaperInput) :
    FPrimeStripEquiv (lgpStrip D) (gauStrip D) :=
  (paperInput D).fLinkAt 1 0 0 1

/-- The actual source link from the core strip to the lower lgp strip. -/
noncomputable def linkLGPToLgpLower (D : S1895PaperInput) :
    FPrimeStripEquiv (lgpStrip D) (lgpLowerStrip D) :=
  (paperInput D).fLinkAt 1 0 1 1

/-- The actual source link from the lower lgp strip to the gau strip. -/
noncomputable def linkLgpLowerToGau (D : S1895PaperInput) :
    FPrimeStripEquiv (lgpLowerStrip D) (gauStrip D) :=
  (paperInput D).fLinkAt 1 1 0 1

/-- The actual source link from the env strip to the gau strip. -/
noncomputable def linkEnvToGau (D : S1895PaperInput) :
    FPrimeStripEquiv (envStrip D) (gauStrip D) :=
  (paperInput D).fLinkAt 0 0 0 1

/-- The factor map from the common group to the env strip, through the actual
link from the core strip. -/
noncomputable def factorEnv (D : S1895PaperInput) (v : PaperV) :
    KummerGroup D →* (envStrip D).toDPrimeStrip.Pi v :=
  (linkLGPToEnv D).isoPi v |>.toMonoidHom.comp (factorLGP D v)

/-- The factor map from the common group to the gau strip, through the actual
link from the core strip. -/
noncomputable def factorGau (D : S1895PaperInput) (v : PaperV) :
    KummerGroup D →* (gauStrip D).toDPrimeStrip.Pi v :=
  (linkLGPToGau D).isoPi v |>.toMonoidHom.comp (factorLGP D v)

/-- The factor map from the common group to the lower lgp strip, through the
actual link from the core strip. -/
noncomputable def factorLgpLower (D : S1895PaperInput) (v : PaperV) :
    KummerGroup D →* (lgpLowerStrip D).toDPrimeStrip.Pi v :=
  (linkLGPToLgpLower D).isoPi v |>.toMonoidHom.comp (factorLGP D v)

/-! ## 3. The actual three legs and the Kummer-evaluation square -/

/-- The upper horizontal evaluation arrow env -> gau, with the actual source
link and the actual strip-equivalence unit portion. -/
noncomputable def upperEvaluation (D : S1895PaperInput) :
    SourceEvaluationArrow (KummerGroup D) (envStrip D) (gauStrip D) :=
  sourceEvaluationArrowOfUnitPortion (linkEnvToGau D)
    (unitPortionOfFactors (G := KummerGroup D) (linkEnvToGau D) (factorEnv D))

/-- The left vertical Kummer arrow LGP -> env. -/
noncomputable def leftKummer (D : S1895PaperInput) :
    SourceKummerArrow (KummerGroup D) (lgpStrip D) (envStrip D) :=
  sourceKummerArrowOfLayer (linkLGPToEnv D)
    (layerOfFactors (G := KummerGroup D) (linkLGPToEnv D) (factorLGP D))

/-- The right vertical Kummer arrow lgp -> gau. -/
noncomputable def rightKummer (D : S1895PaperInput) :
    SourceKummerArrow (KummerGroup D) (lgpLowerStrip D) (gauStrip D) :=
  sourceKummerArrowOfLayer (linkLgpLowerToGau D)
    (layerOfFactors (G := KummerGroup D) (linkLgpLowerToGau D) (factorLgpLower D))

/-- The lower horizontal unit portion, with the actual source link from the
core strip to the lower lgp strip. -/
noncomputable def lowerUnitPortion (D : S1895PaperInput) :
    SourceEvaluationUnitPortion (KummerGroup D) (lgpStrip D) (lgpLowerStrip D) :=
  unitPortionOfFactors (linkLGPToLgpLower D) (factorLGP D)

/-- The actual Kummer-evaluation square on the four actual source strips.  The
lower horizontal is constructed by the paper's conjugation instruction
(ofThreeLegs), with its unit portion taken from the actual lower source link. -/
noncomputable def kummerEvaluationSquare (D : S1895PaperInput) :
    SourceKummerEvaluationSquare (KummerGroup D)
      (envStrip D) (gauStrip D) (lgpStrip D) (lgpLowerStrip D) :=
  SourceKummerEvaluationSquare.ofThreeLegs
    (upperEvaluation D) (leftKummer D) (rightKummer D) (lowerUnitPortion D)

/-- The forced lower horizontal strip representative is exactly the actual
source link fLinkAt 1 0 1 1, not an arbitrary choice. -/
theorem lowerHorizontal_stripIso (D : S1895PaperInput) :
    (kummerEvaluationSquare D).lowerHorizontal.stripIso = linkLGPToLgpLower D := by
  change FPrimeStripEquiv.trans (linkLGPToEnv D)
      (FPrimeStripEquiv.trans (linkEnvToGau D)
        (FPrimeStripEquiv.symm (linkLgpLowerToGau D))) = linkLGPToLgpLower D
  simp only [linkLGPToEnv, linkEnvToGau, linkLgpLowerToGau, linkLGPToLgpLower,
    ((paperInput D).fLinkAt_symm 1 1 0 1)]
  rw [← FPrimeStripEquiv.trans_assoc]
  rw [(paperInput D).fLinkAt_trans 1 0 0 0 0 1]
  rw [(paperInput D).fLinkAt_trans 1 0 0 1 1 1]

/-- The square's two-path equality. -/
theorem kummerEvaluationSquare_twoPath (D : S1895PaperInput) :
    (kummerEvaluationSquare D).domainExpression =
      (kummerEvaluationSquare D).codomainExpression :=
  (kummerEvaluationSquare D).domainExpression_eq_codomainExpression

/-! ## 4. The S1927 packet's four corners and square -/

/-- The four actual source strips packaged as the reduced four corners of the
S1927 packet.  These are actual source lattice strips, not the paper's
F_env/F_gau/F_LGP/F_lgp; the paper-vertex definition is the missing R3 datum
and is not asserted here. -/
structure FourCorners (D : S1895PaperInput) where
  env : FPrimeStrip PaperV
  gau : FPrimeStrip PaperV
  LGP : FPrimeStrip PaperV
  lgp : FPrimeStrip PaperV
  env_eq : env = envStrip D
  gau_eq : gau = gauStrip D
  LGP_eq : LGP = lgpStrip D
  lgp_eq : lgp = lgpLowerStrip D

/-- The actual four corners of the S1895 input. -/
noncomputable def fourCorners (D : S1895PaperInput) : FourCorners D where
  env := envStrip D
  gau := gauStrip D
  LGP := lgpStrip D
  lgp := lgpLowerStrip D
  env_eq := rfl
  gau_eq := rfl
  LGP_eq := rfl
  lgp_eq := rfl

/-- The S1927 Kummer-evaluation square, instantiated at the actual four source
strips and the actual constructed square. -/
noncomputable def s1927Square (D : S1895PaperInput) :
    S1927KummerEvaluationSquareActual D where
  upperLeft := envStrip D
  upperRight := gauStrip D
  lowerLeft := lgpStrip D
  lowerRight := lgpLowerStrip D
  square := kummerEvaluationSquare D

/-- The S1927 packet's parameterized square is inhabited at the actual four
source strips. -/
theorem s1927Square_nonempty (D : S1895PaperInput) :
    Nonempty (S1927KummerEvaluationSquareActual D) :=
  ⟨s1927Square D⟩

/-- The first corner of the S1927 square is the actual source strip used for
the env corner. -/
theorem s1927Square_upperLeft (D : S1895PaperInput) :
    (s1927Square D).upperLeft = envStrip D := rfl

/-- The second corner of the S1927 square is the actual source strip used for
the gau corner. -/
theorem s1927Square_upperRight (D : S1895PaperInput) :
    (s1927Square D).upperRight = gauStrip D := rfl

/-- The third corner of the S1927 square is the actual source strip used for
the LGP corner. -/
theorem s1927Square_lowerLeft (D : S1895PaperInput) :
    (s1927Square D).lowerLeft = lgpStrip D := rfl

/-- The fourth corner of the S1927 square is the actual source strip used for
the lower lgp corner. -/
theorem s1927Square_lowerRight (D : S1895PaperInput) :
    (s1927Square D).lowerRight = lgpLowerStrip D := rfl

/-- The S1927 full log-Kummer package, assembled with the constructed square and
the named archimedean log-shell input. -/
noncomputable def fullLogKummerUQ (D : S1895PaperInput)
    (h : S1927FirstMissing D) : S1927FullLogKummerUQ D :=
  s1927FullLogKummerUQ_of_missing D h (s1927Square D)

/-- The full package's square is the constructed actual square. -/
theorem fullLogKummerUQ_square (D : S1895PaperInput)
    (h : S1927FirstMissing D) :
    (fullLogKummerUQ D h).evaluationSquare = s1927Square D := rfl

/-! ## 5. The exact first missing

The construction above is at the actual source-strip level.  The paper's four
coric vertices F_env, F_gau, F_LGP, F_lgp are not defined in the tree
(SourceKummerEvaluationArrows, R3).  This is a missing *definition*, not a
proposition that can be stated as an equality in the current tree; encoding it
as a free Prop slot or as an empty type would be a fake.  We therefore do not
declare a S1951FirstMissing type or inhabitant.  The four actual source strips
above are labelled env/gau/LGP/lgp only as the reduced source realization, and
no theorem asserts that they are the paper vertices.

The second missing datum is the paper's operation-level content on those
vertices: the Kummer isomorphism of IUT II, Definition 4.9, (i), and the
evaluation isomorphism of IUT II, Corollary 4.10, (ii).  The arrows constructed
above use the actual source links and the strip-equivalence-induced
TimesMuKummer.Isomorphism; they are checked records, but they are not the
paper's operation-level arrows.  The q-pilot anchor identification (R6) is a
third separate missing datum.

Thus the exact first missing is the source definition of the paper's four
coric vertices and of the operation-level Kummer/evaluation arrows on them.
No Lean object for that definition is asserted here; the constructed reduced
square and its S1927 instantiation are the actual content of this file. -/

/-- The constructed upper evaluation arrow is exactly the actual env-to-gau
source link at the strip level. -/
theorem upperEvaluation_stripIso (D : S1895PaperInput) :
    (upperEvaluation D).stripIso = linkEnvToGau D := rfl

/-- The constructed left Kummer arrow is exactly the actual LGP-to-env source
link at the strip level. -/
theorem leftKummer_stripIso (D : S1895PaperInput) :
    (leftKummer D).stripIso = linkLGPToEnv D := rfl

/-- The constructed right Kummer arrow is exactly the actual lgp-to-gau source
link at the strip level. -/
theorem rightKummer_stripIso (D : S1895PaperInput) :
    (rightKummer D).stripIso = linkLgpLowerToGau D := rfl

/-! ## 6. Dependency probes -/

#print axioms fourCorners
#print axioms lowerHorizontal_stripIso
#print axioms kummerEvaluationSquare
#print axioms kummerEvaluationSquare_twoPath
#print axioms s1927Square
#print axioms s1927Square_nonempty
#print axioms fullLogKummerUQ
#print axioms upperEvaluation_stripIso
#print axioms leftKummer_stripIso
#print axioms rightKummer_stripIso

end LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
