import PolyFit.Objective

/-!
# Moves for the local search

The offsets used by the fine and ultra-fine searches (`Polish.lean`): a move shifts
vertices by offsets in `{-1, 0, 1}²`.
-/

namespace PolyFit

instance : Add Pt := ⟨fun p q => ⟨p.i + q.i, p.j + q.j⟩⟩

/-- The 9 offsets `{-1, 0, 1}²`, including `(0, 0)`. -/
def unitOffsets : Array Pt :=
  #[-1, 0, 1].flatMap fun a => #[-1, 0, 1].map fun b => ⟨a, b⟩

end PolyFit
