import Reciprocity.Artin
import Reciprocity.ArtinContinuous
import Reciprocity.ArtinInertia
import Reciprocity.ArtinUnique
import Reciprocity.NormCompat
import Reciprocity.BaseChange

/-!
S2052 acceptance probe: the ported local CFT Artin map and its finite reciprocity
statements must be usable from the current project.
-/

#check @PadicField.artin
#check @PadicField.artinEquiv
#check @PadicField.artin_apply
#check @PadicField.artin_apply_eq_self_iff
#check @PadicField.mem_ker_artin_iff
#check @PadicField.abRec
#check @PadicField.artin_injective
#check @PadicField.denseRange_artin
#check @PadicField.unitsInertiaEquiv
#check @PadicField.eq_artin_iff
#check @PadicField.continuous_artin
#check @PadicField.artin_baseChange
#check @PadicField.artin_apply_maxUnramified_of_v_eq_one
#check @PadicField.mk_eq_arithFrob_of_artin

#print axioms PadicField.artin
#print axioms PadicField.artin_apply_eq_self_iff
#print axioms PadicField.artin_injective
#print axioms PadicField.denseRange_artin
#print axioms PadicField.eq_artin_iff
#print axioms PadicField.continuous_artin
#print axioms PadicField.artin_baseChange
#print axioms PadicField.unitsInertiaEquiv
