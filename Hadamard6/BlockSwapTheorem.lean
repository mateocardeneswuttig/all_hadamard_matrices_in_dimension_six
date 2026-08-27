import Hadamard6.BlockPermutations
import Hadamard6.BlockSwapInfiniteSquare

/-!
# The finite-or-infinite block-swap theorem

At each of the three relevant corners, either both adjacent normalized Gram
fibres are finite, producing an actual retained finite corner, or at least one
is infinite.  If all three corners take the latter option, the complete
infinite-fibre square forces all four blocks to be Hadamard.
-/

namespace Hadamard6

variable {IsKarlsson : Mat6 → Prop}

theorem blockSwap_from_twoByTwo_input
    (htwo : TwoByTwoKarlssonCriterion IsKarlsson) :
    ∀ H, IsHadamard H → ¬ IsKarlsson H →
      HasFiniteCorner H ∨ AllFourBlocksHadamard H := by
  intro H hH hK
  rcases all_four_blocks_det_ne_zero htwo hH hK with
    ⟨hdetE, hdetB, hdetC, hdetD⟩
  let BRow := normalizedRowGramFibre
    (Matrix.toBlocks₁₂ H * Matrix.conjTranspose (Matrix.toBlocks₁₂ H))
  let CCol := normalizedColumnGramFibre
    (Matrix.conjTranspose (Matrix.toBlocks₂₁ H) * Matrix.toBlocks₂₁ H)
  let ERow := normalizedRowGramFibre
    (Matrix.toBlocks₁₁ H * Matrix.conjTranspose (Matrix.toBlocks₁₁ H))
  let DCol := normalizedColumnGramFibre
    (Matrix.conjTranspose (Matrix.toBlocks₂₂ H) * Matrix.toBlocks₂₂ H)
  let ECol := normalizedColumnGramFibre
    (Matrix.conjTranspose (Matrix.toBlocks₁₁ H) * Matrix.toBlocks₁₁ H)
  let DRow := normalizedRowGramFibre
    (Matrix.toBlocks₂₂ H * Matrix.conjTranspose (Matrix.toBlocks₂₂ H))
  by_cases hAtE : BRow.Infinite ∨ CCol.Infinite
  · by_cases hAtB : ERow.Infinite ∨ DCol.Infinite
    · by_cases hAtC : ECol.Infinite ∨ DRow.Infinite
      · exact Or.inr (infinite_fibre_block_square_forces_allFour htwo hH hK
          (by simpa [BRow, CCol] using hAtE)
          (by simpa [ERow, DCol] using hAtB)
          (by simpa [ECol, DRow] using hAtC))
      · push Not at hAtC
        exact Or.inl (finite_bottomLeft_intrinsic_fibres_give_finiteCorner
          hH hdetE hdetC hdetD
          (by simpa [ECol] using hAtC.1)
          (by simpa [DRow] using hAtC.2))
    · push Not at hAtB
      exact Or.inl (finite_topRight_intrinsic_fibres_give_finiteCorner
        hH hdetE hdetB hdetD
        (by simpa [ERow] using hAtB.1)
        (by simpa [DCol] using hAtB.2))
  · push Not at hAtE
    exact Or.inl (finite_topLeft_intrinsic_fibres_give_finiteCorner
      hH hdetE hdetB hdetC
      (by simpa [BRow] using hAtE.1)
      (by simpa [CCol] using hAtE.2))

end Hadamard6
