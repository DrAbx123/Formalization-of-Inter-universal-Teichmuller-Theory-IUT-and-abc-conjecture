import PadicField.UnramifiedZHat
import PadicField.AbsoluteInertia
import PadicField.Powers

/-!
S2051 verification probe: import the ported unramified layer and print the axiom
footprints of its main declarations. This file is a check artifact, not part of the port.
-/

#print axioms PadicField.maxUnramified
#print axioms PadicField.frobUr
#print axioms PadicField.dense_zpowers_frobUr
#print axioms PadicField.gal_maxUnramified_mul_comm
#print axioms PadicField.exists_restrict_eq
#print axioms PadicField.IsUnramified
#print axioms PadicField.adjoin_teichmullerSet_eq_top
#print axioms PadicField.galMaxUnramifiedEquiv
#print axioms PadicField.galMaxUnramifiedEquiv_frobUr
#print axioms PadicField.absInertia_eq
#print axioms PadicField.unramifiedQuotientEquiv
#print axioms PadicField.instIsAdicComplete
#print axioms PadicField.isGalois_of_isUnramified
#print axioms PadicField.residueGalEquiv
