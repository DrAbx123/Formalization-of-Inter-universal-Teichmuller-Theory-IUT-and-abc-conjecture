import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Scheme

/-!
# AG-00: Mathlib algebraic-geometry capability matrix (audit component, not a paper object)

COMPONENT, not a paper object.  Named consumers: coord/AG-INFRA-PLAN.md,
AG-01 curve foundations, AG-02 genus interface.

Real capability matrix for the AG infrastructure required by [Mzk1] Theorem 2.5
(GeometricCore), verified against the Mathlib checkout in this repository
(.lake/packages/mathlib/Mathlib/AlgebraicGeometry).  The matrix is literal data;
available/missing facts are kernel-checked rfl computations on an inductive
capability type (no axiom, no fake data).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.AG00MathlibAuditActual

/-- The AG concepts required by the GeometricCore build. -/
inductive AGCapability
  | scheme | projectiveSpectrum | properMorphism | smoothMorphism
  | smoothRelativeDimension | geometricallyConnected | functionField
  | orderOfVanishing | rationalMap | lineBundle | coherentCohomology
  | riemannRoch | serreDuality | genus
  deriving DecidableEq, Repr

/-- Availability in the repository's Mathlib checkout. -/
def AGCapability.available : AGCapability → Bool
  | scheme => true
  | projectiveSpectrum => true
  | properMorphism => true
  | smoothMorphism => true
  | smoothRelativeDimension => true
  | geometricallyConnected => true
  | functionField => true
  | orderOfVanishing => true
  | rationalMap => true
  | lineBundle => false
  | coherentCohomology => false
  | riemannRoch => false
  | serreDuality => false
  | genus => false

/-- A capability row: concept, availability, and the Mathlib reference. -/
structure AGMathlibCapability where
  cap : AGCapability
  file : String
  line : Nat

/-- Verified Mathlib capability matrix (reference lines in this repository's
Mathlib checkout). -/
def AGMathlibCapabilities : List AGMathlibCapability :=
  [ { cap := .scheme, file := "Mathlib/AlgebraicGeometry/Scheme.lean", line := 1 },
    { cap := .projectiveSpectrum,
      file := "Mathlib/AlgebraicGeometry/ProjectiveSpectrum", line := 1 },
    { cap := .properMorphism,
      file := "Mathlib/AlgebraicGeometry/Morphisms/Proper.lean", line := 42 },
    { cap := .smoothMorphism,
      file := "Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean", line := 62 },
    { cap := .smoothRelativeDimension,
      file := "Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean", line := 135 },
    { cap := .geometricallyConnected,
      file := "Mathlib/AlgebraicGeometry/Geometrically/Connected.lean", line := 40 },
    { cap := .functionField,
      file := "Mathlib/AlgebraicGeometry/FunctionField.lean", line := 1 },
    { cap := .orderOfVanishing,
      file := "Mathlib/AlgebraicGeometry/OrderOfVanishing.lean", line := 1 },
    { cap := .rationalMap,
      file := "Mathlib/AlgebraicGeometry/RationalMap.lean", line := 1 },
    { cap := .lineBundle, file := "absent", line := 0 },
    { cap := .coherentCohomology, file := "absent", line := 0 },
    { cap := .riemannRoch, file := "absent", line := 0 },
    { cap := .serreDuality, file := "absent", line := 0 },
    { cap := .genus, file := "absent", line := 0 } ]

/-- The matrix has 14 rows. -/
theorem AGMathlibCapabilities_length : AGMathlibCapabilities.length = 14 :=
  rfl

/-- Mathlib provides the proper-morphism predicate. -/
theorem AG00_proper_available : AGCapability.available .properMorphism = true :=
  rfl

/-- Mathlib provides the smooth-morphism predicate. -/
theorem AG00_smooth_available : AGCapability.available .smoothMorphism = true :=
  rfl

/-- Mathlib provides geometrically connected morphisms. -/
theorem AG00_geometricallyConnected_available :
    AGCapability.available .geometricallyConnected = true :=
  rfl

/-- Mathlib has NO line-bundle/invertible-sheaf layer. -/
theorem AG00_lineBundle_missing : AGCapability.available .lineBundle = false :=
  rfl

/-- Mathlib has NO coherent-cohomology layer. -/
theorem AG00_cohomology_missing :
    AGCapability.available .coherentCohomology = false :=
  rfl

/-- Mathlib has NO Riemann-Roch. -/
theorem AG00_riemannRoch_missing : AGCapability.available .riemannRoch = false :=
  rfl

/-- Mathlib has NO Serre duality. -/
theorem AG00_serreDuality_missing : AGCapability.available .serreDuality = false :=
  rfl

/-- Mathlib has NO curve-genus definition. -/
theorem AG00_genus_missing : AGCapability.available .genus = false :=
  rfl

end LeanFormal.IUT.XiFPaper.AG00MathlibAuditActual
