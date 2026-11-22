import LeanFormal.IUT.Audit.Status

/-!
# S3138: audit cards for the source-level Step XI bridge

Machine-readable status cards for the stepxi stream.  They are deliberately
conservative:

* the genuine source projections are `sourceProjection` (a proved projection
  from the supplied `OriginalInput` plus proved parametric theorems);
* the Step XI contracts stay `conditional` (the paper's two arithmetic
  comparisons and the IPL/SHE/APT evidence remain explicit arguments);
* the signed (xi-f) hull comparison stays `interface` (exact missing object,
  no supplier).
-/

namespace LeanFormal.IUT.Audit

/-- The actual source procession core / profile / carrier / Step XI input built
from a genuine `OriginalInput` (no finite-model surrogate). -/
def sourceStepXISourceCarrier : Obligation :=
  { id := "IUT-III.source-stepXI-source-carrier"
    source :=
      "IUT III, Theorem 3.11 (procession and Ind1/Ind2/Ind3); IUT I, Hodge-theater histories; IUT II (Theta packets)"
    status := VerificationStatus.sourceProjection
    note :=
      "From any OriginalInput this module constructs: the source Core on " ++
        "ZZ x ZZ labels with the actual lattice translations I.translate; the " ++
        "actual source Profile (theater Theta log-volume, constant on the " ++
        "family by family link q-transport and FiniteThetaPacket.log_scale); " ++
        "the same-level connector along the actual translations; the actual " ++
        "ParametricTheorem311.Carrier; and the actual " ++
        "SourceProcessionBoundary.Input (theater at (n,m), reflexive singleton " ++
        "dependent history, actual base theta log-volume, route normal form " ++
        "from routeTarget_level_eq_budget). No finite Q(i)-at-5 surrogate is " ++
        "used. The level coordinate is the repo's Ind3-height modeling device " ++
        "(same shape as the finite ProcessionChoice), not a paper object."
    dependsOn :=
      [ "IUT-I.hodge-theater-history-composition",
        "IUT-III.source-procession-boundary",
        "IUT-III.parametric-carrier-route-kernel" ] }

/-- The actual Theorem 3.11 certificate and the V1/V2 pinned Step XI boundaries
over the source input. -/
def sourceStepXISourceAssembly : Obligation :=
  { id := "IUT-III.source-stepXI-source-assembly"
    source :=
      "IUT III, Theorem 3.11 -> Corollary 3.12, Steps (xi-a)-(xi-f)"
    status := VerificationStatus.conditional
    note :=
      "Over the actual source Step XI input this module proves the D-stage " ++
        "wall (routeWall), its run identity, the normalized wall, the actual " ++
        "Theorem 3.11 certificate (source profile = theater theta log-volume, " ++
        "Ind1/Ind2/Ind3 route evidence, route normalization), the V1 and V2 " ++
        "pinned arithmetic links from the single (xi-f)-shaped inclusion " ++
        "q <= hullValue, and the assembled boundaries with the Corollary 3.12 " ++
        "ordered conclusion. The two arithmetic comparisons and the " ++
        "IPL/SHE/APT evidence remain explicit arguments: this card does not " ++
        "claim the signed comparison -|log q| <= -|log Theta|."
    dependsOn :=
      [ "IUT-III.source-stepXI-source-carrier",
        "IUT-III.source-procession-stepXI-boundary",
        "IUT-III.parametric-StepXI-assembly" ] }

/-- The exact missing signed hull carrier of Step (xi-f). -/
def sourceStepXISignedHullResidual : Obligation :=
  { id := "IUT-III.source-stepXI-signed-hull-residual"
    source :=
      "IUT III, Corollary 3.12 proof, Steps (xi-d)-(xi-f); IUT IV, Theorem 1.10"
    status := VerificationStatus.interface
    note :=
      "Exact residual: a signed real hull-log-volume carrier for 1,circ U with " ++
        "value -|log Theta| < 0 and a signed q-pilot log-volume -|log q| < 0, " ++
        "together with the inclusion between them. The tree supplies only an " ++
        "ENNReal-valued IQ log-volume (nonnegative real part); on that carrier " ++
        "the inclusion is automatic (zero discriminating power). Proved here: " ++
        "the inclusion is equivalent to |log Theta| <= |log q| and to " ++
        "1 <= C_Theta = |log q| / |log Theta|; it is invariant under " ++
        "simultaneous positive rescaling; sign data alone does not determine " ++
        "it; a supplied SignedHullRealization yields the Corollary 3.12 " ++
        "contract. No supplier, no axiom, no sorry."
    dependsOn :=
      [ "IUT-III.source-procession-stepXI-xif-inclusion",
        "IUT-III.holomorphic-hull-determinant-log-volume" ] }

/-- Identity anchoring of the (SHE) transport laws. -/
def sourceStepXISHEUnit : Obligation :=
  { id := "IUT-III.source-stepXI-SHE-transport-unit"
    source :=
      "IUT III, Remark 3.11.1, (iii) (SHE); Corollary 3.12, proof Step (xi-b)"
    status := VerificationStatus.provedKernel
    note :=
      "Conjugation of an F-prime-strip fiber link by identity strip " ++
        "equivalences is the identity on the index/Pi/G/Mon fibers; hence the " ++
        "simultaneity square transported along the identity quadruple is a " ++
        "simultaneity square and the (xi-b) consumer wiring applies at the " ++
        "identity transport. Cardinal-SHE source obligations (Kummer legs, " ++
        "1,circ binding, hull expression, times-mu upgrade) remain open."
    dependsOn := [ "IUT-III.SHE" ] }

end LeanFormal.IUT.Audit
