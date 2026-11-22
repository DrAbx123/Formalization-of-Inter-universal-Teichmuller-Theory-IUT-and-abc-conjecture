import tmp.sheaf.n8.closure.PaperInitialThetaDataFull
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Actual paper orbicurve clause construction

Actual fields from ClauseD:
- exact sequence from xK_exact_sequence (profinite sequence projected to the
  SourceExactSequenceClause four slots);
- structure group from the xK exact sequence galois group;
- cuspCount from the actual xF once-punctured elliptic signature;
- curveCompatibility from ClauseD.xK_cK_cartesian_square.
The curve type is the actual PuncturedEllipticCurve F type.

Precise donor fields (no arbitrary fill): puncturedCurve and cover carriers,
the two maps, and cover surjectivity.  These are exactly the geometric
morphism fields not supplied by ClauseD's signature-level data.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source

namespace LeanFormal.IUT.N8Closure.PaperOrbicurveClauseActual

universe u

variable {l : PrimeGeFive} (S : SourceInitialThetaData.{0} l)
variable (C : ClauseD l S.candidate)

noncomputable def sourceGroupHomToMonoidHom
    {G H : SourceGroup} (f : SourceGroupHom G H) :
    G.carrier →* H.carrier where
  toFun := f.map
  map_one' := f.map_one
  map_mul' := f.map_mul

/-- Actual SourceExactSequenceClause projection from a profinite sequence. -/
noncomputable def paperExactSequence
    (E : SourceProfiniteExactSequence) :
    SourceExactSequenceClause.{0, 0, 0} where
  baseGroup := E.galois.carrier
  coverGroup := E.arithmetic.carrier
  geometricGroup := E.geometric.carrier
  injection := sourceGroupHomToMonoidHom E.injection
  projection := sourceGroupHomToMonoidHom E.projection
  injection_injective := E.injection_injective
  projection_surjective := E.projection_surjective
  exact_at_cover := E.exact_at_arithmetic
  sectionMap := sourceGroupHomToMonoidHom E.sectionMap
  section_right_inverse := E.section_right_inverse

/-- Actual cusp count from the xF once-punctured elliptic signature. -/
def paperCuspCount : Nat :=
  S.candidate.xF.signature.punctures

theorem paperCuspCount_pos (C : ClauseD l S.candidate) :
    0 < paperCuspCount S := by
  rw [paperCuspCount, C.xF_type]
  decide

/-- Exact geometric donors for the fields not present in ClauseD signatures. -/
structure PaperOrbicurveDonors (S : SourceInitialThetaData.{0} l) where
  puncturedCurve : Type
  cover : Type
  curveToPunctured : puncturedCurve →
    PuncturedEllipticCurve S.candidate.arithmetic.F
  coverToPunctured : cover → puncturedCurve
  cover_surjective : Function.Surjective coverToPunctured

/-- Conditional actual SourceOrbicurveClause: curve/exact sequence/structure
group/cuspCount/compatibility actual; only the geometric carriers and maps are
donors. -/
noncomputable def paperOrbicurveClause
    (D : PaperOrbicurveDonors S) :
    SourceOrbicurveClause.{0, 0, 0} where
  curve := PuncturedEllipticCurve S.candidate.arithmetic.F
  puncturedCurve := D.puncturedCurve
  cover := D.cover
  structureGroup := C.xK_exact_sequence.galois.carrier
  curveToPunctured := D.curveToPunctured
  coverToPunctured := D.coverToPunctured
  cover_surjective := D.cover_surjective
  exactSequence := paperExactSequence C.xK_exact_sequence
  cuspCount := paperCuspCount S
  cuspCount_pos := paperCuspCount_pos S C
  curveCompatibility := C.xK_cK_cartesian_square
  curveCompatibility_proved := C.xK_cK_cartesian_square_proved

/-- Exact field gap: ClauseD gives no geometric maps/carriers for the
punctured curve and its cover, only signatures, orbicurve objects and group
exact sequences. -/
def PaperOrbicurveMapGap : Prop :=
  ¬ Nonempty (PaperOrbicurveDonors S)

end LeanFormal.IUT.N8Closure.PaperOrbicurveClauseActual

end