import Hadamard6.Blocks
import Hadamard6.BlockSwapTheorem

/-!
# Failed-search routing core

This internal layer has exactly two alternatives:

* the matrix belongs to the previously classified exceptional sector
  (`IsKarlsson ∨ IsTao`); or
* it belongs to the independently defined finite-corner atlas.

The paper-facing witness theorem is in `PaperTheorem.lean`; this file only
supplies its reusable routing reduction.  The predicates naming the Karlsson
sector and Tao orbit remain parameters so this argument is independent of
their concrete representations.
-/

namespace Hadamard6

variable (IsTao IsKarlsson : Mat6 → Prop)

/-- If block swapping reaches either a finite corner or the classified
all-Fourier branch, then every Hadamard matrix lies in an exceptional sector
or in the finite-corner atlas. -/
theorem exceptional_or_finiteCornerAtlas_of_routing
    (hblockSwap :
      ∀ H, IsHadamard H → ¬ IsKarlsson H →
        HasFiniteCorner H ∨ AllFourBlocksHadamard H)
    (hfourierBlocks :
      ∀ H, IsHadamard H → AllFourBlocksHadamard H →
        InKnownExceptionalSector IsTao IsKarlsson H) :
    ∀ H : Mat6, IsHadamard H →
      InKnownExceptionalSector IsTao IsKarlsson H ∨
        InFiniteCornerAtlas H := by
  intro H hH
  by_cases hKarlsson : IsKarlsson H
  · exact Or.inl (Or.inl hKarlsson)
  rcases hblockSwap H hH hKarlsson with hfinite | hfourier
  · exact Or.inr (finiteCorner_mem_finiteCornerAtlas hfinite)
  · exact Or.inl (hfourierBlocks H hH hfourier)

end Hadamard6
