import PNP

/-! Run `lake env lean Axioms.lean`. Each theorem should report exactly
`propext`, `Classical.choice` and `Quot.sound`. -/

#print axioms PNP.parity_exact_without_xor
#print axioms PNP.Full.hard_needs_two_per_input
#print axioms PNP.Full.atLeastTwo_needs_two_gates_per_input
