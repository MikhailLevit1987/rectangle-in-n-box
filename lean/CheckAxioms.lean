import RectInNBox

/-! Run with `lake env lean CheckAxioms.lean`. Expected output for each theorem:
`depends on axioms: [propext, Classical.choice, Quot.sound]` (no `sorryAx`). -/

#print axioms RectInNBox.fitsN_rect_iff_explicit
#print axioms RectInNBox.fitsN_rect_iff_condII
#print axioms RectInNBox.fits2_iff_carver
#print axioms RectInNBox.fitsN_rect_iff
#print axioms RectInNBox.fitsN_iff_widths
