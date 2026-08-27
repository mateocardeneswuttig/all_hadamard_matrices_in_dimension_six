import Hadamard6.BlockFibreNormalizedOutcome
import Hadamard6.FiniteCornerConsequences

/-!
# The complete infinite-fibre block square

This is the combinatorial heart of the block-swap argument.  At the upper
left block choose an infinite horizontal or vertical complementary fibre.
At the adjacent corner choose the next infinite fibre.  The checked sign
lemmas exclude both choices unless all four blocks are Hadamard.
-/

namespace Hadamard6

variable {IsKarlsson : Mat6 → Prop}

theorem infinite_fibre_block_square_forces_allFour
    (htwo : TwoByTwoKarlssonCriterion IsKarlsson)
    {H : Mat6} (hH : IsHadamard H) (hK : ¬ IsKarlsson H)
    (hAtE :
      (normalizedRowGramFibre
        (Matrix.toBlocks₁₂ H *
          Matrix.conjTranspose (Matrix.toBlocks₁₂ H))).Infinite ∨
      (normalizedColumnGramFibre
        (Matrix.conjTranspose (Matrix.toBlocks₂₁ H) *
          Matrix.toBlocks₂₁ H)).Infinite)
    (hAtB :
      (normalizedRowGramFibre
        (Matrix.toBlocks₁₁ H *
          Matrix.conjTranspose (Matrix.toBlocks₁₁ H))).Infinite ∨
      (normalizedColumnGramFibre
        (Matrix.conjTranspose (Matrix.toBlocks₂₂ H) *
          Matrix.toBlocks₂₂ H)).Infinite)
    (hAtC :
      (normalizedColumnGramFibre
        (Matrix.conjTranspose (Matrix.toBlocks₁₁ H) *
          Matrix.toBlocks₁₁ H)).Infinite ∨
      (normalizedRowGramFibre
        (Matrix.toBlocks₂₂ H *
          Matrix.conjTranspose (Matrix.toBlocks₂₂ H))).Infinite) :
    AllFourBlocksHadamard H := by
  rcases all_four_blocks_det_ne_zero htwo hH hK with
    ⟨hdetE, hdetB, hdetC, hdetD⟩
  rcases hAtE with hBinf | hCinf
  · have hBout := topRight_infinite_gram_fibre_outcome htwo hH rfl hBinf hdetB
    rcases hAtB with hEinf | hDinf
    · have hEout := topLeft_infinite_gram_fibre_outcome htwo hH rfl hEinf hdetE
      exact two_horizontal_outcomes_force_allFour IsKarlsson hH hK hBout hEout
    · have hDout := bottomRight_infinite_column_gram_fibre_outcome
        htwo hH rfl hDinf hdetD
      exact horizontal_and_opposite_vertical_outcomes_force_allFour
        IsKarlsson hH hK hBout hDout
  · have hCout := bottomLeft_infinite_column_gram_fibre_outcome
      htwo hH rfl hCinf hdetC
    rcases hAtC with hEinf | hDinf
    · have hEout := topLeft_infinite_column_gram_fibre_outcome
        htwo hH rfl hEinf hdetE
      exact two_vertical_outcomes_force_allFour IsKarlsson hH hK hCout hEout
    · have hDout := bottomRight_infinite_row_gram_fibre_outcome
        htwo hH rfl hDinf hdetD
      exact vertical_and_opposite_horizontal_outcomes_force_allFour
        IsKarlsson hH hK hCout hDout

end Hadamard6
