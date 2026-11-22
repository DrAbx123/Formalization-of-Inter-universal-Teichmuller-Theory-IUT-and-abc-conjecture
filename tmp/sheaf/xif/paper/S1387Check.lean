import tmp.sheaf.xif.paper.S1387D9PaperSlotActual

/-! Independent consumer check for S1387.  This file is not source; it only
imports the compiled S1387 module and re-checks the exported first-field and
slot interfaces plus their axiom footprints. -/

open LeanFormal.IUT.XiFPaper.S1387D9PaperSlotActual

#check @S1387D9FirstField
#check @S1387D9Remainder
#check @S1387D9StackFirstField
#check @S1387D9FirstFieldOfFiber
#check @S1387D9FirstField_nonempty_iff_stackFirstField
#check @S1387D9FirstFieldOfMissingD6
#check @S1387D9FirstFieldOfPaperClause
#check @S1387D9SlotOfPaperClause
#check @S1387PaperSlotEquiv
#check @S1387D9SlotEquiv
#check @S1387D9Slot_nonempty_iff
#check @S1387D9SlotOfMissingD6
#check @S1387D9Slot_nonempty_of_missingD6
#check @S1387D9FirstFieldOfS1348
#check @S1387D9SlotOfS1348
#check @S1387S1348FirstFieldOfD9
#check @S1387D9FirstField_not_pointFiber
#check @S1387D9FirstField_not_terminal
#check @S1387NoTerminalCarrier

#print axioms S1387D9FirstFieldOfFiber
#print axioms S1387D9FirstFieldOfMissingD6
#print axioms S1387D9FirstFieldOfPaperClause
#print axioms S1387D9SlotOfPaperClause
#print axioms S1387PaperSlotEquiv
#print axioms S1387D9SlotEquiv
#print axioms S1387D9Slot_nonempty_iff
#print axioms S1387D9SlotOfMissingD6
#print axioms S1387D9Slot_nonempty_of_missingD6
#print axioms S1387D9FirstFieldOfS1348
#print axioms S1387D9SlotOfS1348
#print axioms S1387S1348FirstFieldOfD9
#print axioms S1387D9FirstField_not_pointFiber
#print axioms S1387D9FirstField_not_terminal
#print axioms S1387NoTerminalCarrier
