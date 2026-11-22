/-
Fresh-gate probe: imports every module that compiled green in this gate and
prints the axioms of one main theorem each. Generated for this run only.
-/
import tmp.sheaf.xif.paper.S1268HDDLatticeActual
import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
import tmp.sheaf.xif.paper.S1126MultiradialAuditActual
import tmp.sheaf.xif.paper.S1305HDDLatticeFromHullDetExact
import tmp.sheaf.xif.paper.S1356HDDHullDetSourceActual
import tmp.sheaf.xif.paper.S1418HDDConsumerActual
import tmp.sheaf.xif.paper.S1275SHEDDNonLatticeFieldsActual

-- S1305 defines only an abbrev (no theorem); checked, no axiom query possible.
#check LeanFormal.IUT.XiFPaper.S1305HDDLatticeFromHullDetExact.S1305HDDLocalLatticeExactType

#print axioms LeanFormal.IUT.XiFPaper.S1268HDDLatticeActual.s1268LocalizeSection_eq_unitSection_of_injective
#print axioms LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual.modelHull_subset_paperSHull
#print axioms LeanFormal.IUT.XiFPaper.S1126MultiradialAuditActual.s1126CurrentUnion_eq_theta
#print axioms LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual.s1356LatticeOfSource
#print axioms LeanFormal.IUT.XiFPaper.S1418HDDConsumerActual.s1418GlobalLattice_eq_hull
#print axioms LeanFormal.IUT.XiFPaper.S1275SHEDDNonLatticeFieldsActual.s1275SHELocalization_output
