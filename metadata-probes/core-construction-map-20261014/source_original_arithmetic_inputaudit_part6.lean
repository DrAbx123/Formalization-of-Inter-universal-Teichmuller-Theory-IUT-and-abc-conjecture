/-
  Owned audit probe #7 for source_original_arithmetic_input-v1
  (run core-construction-map-20261014, agent dsh_original_input_owner).

  Types of the Definition 3.1 arithmetic-compatibility fields and of the
  primed-strip carrier.  No bodies, no sibling source reads.
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.InitialThetaInputCore
import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary

set_option linter.unusedVariables false

namespace LeanFormal.IUT.AuditProbe7

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

#check @SourceDefinition31Data.source_curve_bundle
#check @SourceDefinition31Data.arithmetic_reduction_compatibility
#check @SourceDefinition31Data.arithmetic_torsion_compatibility
#check @SourceDefinition31Data.arithmetic_orbicurve_compatibility
#check @SourceDefinition31Data.arithmetic_section_compatibility
#check @SourceDefinition31Data.arithmetic_cusp_compatibility
#check @SourceDefinition31Data.arithmetic_reduction_spec
#check @SourceDefinition31Data.arithmetic_orbicurve_spec
#check @SourceDefinition31Data.arithmetic_torsion_spec
#check @SourceDefinition31Data.arithmetic_section_spec
#check @SourceDefinition31Data.arithmetic_cusp_spec

/-! ## Prime strip carriers of HodgeTheater / HodgeTheaterLink -/

#check @HodgeTheater.primeStrip
#check @FPrimeStrip
#check @FPrimeStrip.monoAnalytic
#check @FPrimeStrip.toDPrimeStrip
#check @FPrimeStrip.Mon
#check @FPrimeStrip.proj
#check @FPrimeStrip.action
#check @FPrimeStrip.degree
#check @FPrimeStrip.G
#check @HodgeTheaterLink.primeStripEquiv
#check @FPrimeStripEquiv
#check @FPrimeStripEquiv.isoPi
#check @FPrimeStripEquiv.isoG
#check @FPrimeStripEquiv.isoMon
#check @FPrimeStripEquiv.compatProj_apply

/-! ## Theorem 3.11 output record fields -/

#check @Theorem311Output
#check @Theorem311Output.labelled
#check @Theorem311Output.horizontal
#check @Theorem311Output.evaluation

end LeanFormal.IUT.AuditProbe7
