import Hadamard6.NormalizedBlockOpposite
import Hadamard6.BlockSwapCore

/-!
# Intrinsically normalized block-fibre outcomes
-/

namespace Hadamard6

variable {IsKarlsson : Mat6 → Prop}

theorem topRight_infinite_gram_fibre_outcome
    (htwo : TwoByTwoKarlssonCriterion IsKarlsson)
    {H : Mat6} (hH : IsHadamard H) {G : Mat3}
    (hgram : Matrix.toBlocks₁₂ H *
      Matrix.conjTranspose (Matrix.toBlocks₁₂ H) = G)
    (hinf : (normalizedRowGramFibre G).Infinite)
    (hdet : (Matrix.toBlocks₁₂ H).det ≠ 0) :
    RowFibreOutcome IsKarlsson H (Matrix.toBlocks₁₂ H) := by
  let B := Matrix.toBlocks₁₂ H
  have hBu := (hadamard_blocks_entrywiseUnit hH).2.1
  have hmem := normalizeFirstRow_mem_fibre hBu hgram
  have hdet' := normalizeFirstRow_det_ne_zero hBu hdet
  rcases infinite_row_fibre_trichotomy hinf hmem hdet' with
    hfour | hneg | hopp
  · exact Or.inl ((normalizeFirstRow_isHadamard3_iff hBu).mp hfour)
  · right; left
    rw [rowTau_normalizeFirstRow hBu] at hneg
    exact hneg
  · right; right
    exact htwo H hH
      (normalizedTopRight_opposite_hasHadamardTwoByTwo hH hopp)

theorem topLeft_infinite_gram_fibre_outcome
    (htwo : TwoByTwoKarlssonCriterion IsKarlsson)
    {H : Mat6} (hH : IsHadamard H) {G : Mat3}
    (hgram : Matrix.toBlocks₁₁ H *
      Matrix.conjTranspose (Matrix.toBlocks₁₁ H) = G)
    (hinf : (normalizedRowGramFibre G).Infinite)
    (hdet : (Matrix.toBlocks₁₁ H).det ≠ 0) :
    RowFibreOutcome IsKarlsson H (Matrix.toBlocks₁₁ H) := by
  let E := Matrix.toBlocks₁₁ H
  have hEu := (hadamard_blocks_entrywiseUnit hH).1
  have hmem := normalizeFirstRow_mem_fibre hEu hgram
  have hdet' := normalizeFirstRow_det_ne_zero hEu hdet
  rcases infinite_row_fibre_trichotomy hinf hmem hdet' with
    hfour | hneg | hopp
  · exact Or.inl ((normalizeFirstRow_isHadamard3_iff hEu).mp hfour)
  · right; left
    rw [rowTau_normalizeFirstRow hEu] at hneg
    exact hneg
  · right; right
    exact htwo H hH
      (normalizedTopLeft_opposite_hasHadamardTwoByTwo hH hopp)

theorem bottomRight_infinite_column_gram_fibre_outcome
    (htwo : TwoByTwoKarlssonCriterion IsKarlsson)
    {H : Mat6} (hH : IsHadamard H) {G : Mat3}
    (hgram : Matrix.conjTranspose (Matrix.toBlocks₂₂ H) *
      Matrix.toBlocks₂₂ H = G)
    (hinf : (normalizedColumnGramFibre G).Infinite)
    (hdet : (Matrix.toBlocks₂₂ H).det ≠ 0) :
    ColumnFibreOutcome IsKarlsson H (Matrix.toBlocks₂₂ H) := by
  let D := Matrix.toBlocks₂₂ H
  have hDu := (hadamard_blocks_entrywiseUnit hH).2.2.2
  have hmem := normalizeFirstColumn_mem_fibre hDu hgram
  have hdet' := normalizeFirstColumn_det_ne_zero hDu hdet
  rcases infinite_column_fibre_trichotomy hinf hmem hdet' with
    hfour | hneg | hopp
  · exact Or.inl ((normalizeFirstColumn_isHadamard3_iff hDu).mp hfour)
  · right; left
    rw [columnTau_normalizeFirstColumn_re hDu] at hneg
    exact hneg
  · right; right
    exact htwo H hH
      (normalizedBottomRight_oppositeColumn_hasHadamardTwoByTwo hH hopp)

theorem bottomRight_infinite_row_gram_fibre_outcome
    (htwo : TwoByTwoKarlssonCriterion IsKarlsson)
    {H : Mat6} (hH : IsHadamard H) {G : Mat3}
    (hgram : Matrix.toBlocks₂₂ H *
      Matrix.conjTranspose (Matrix.toBlocks₂₂ H) = G)
    (hinf : (normalizedRowGramFibre G).Infinite)
    (hdet : (Matrix.toBlocks₂₂ H).det ≠ 0) :
    RowFibreOutcome IsKarlsson H (Matrix.toBlocks₂₂ H) := by
  let D := Matrix.toBlocks₂₂ H
  have hDu := (hadamard_blocks_entrywiseUnit hH).2.2.2
  have hmem := normalizeFirstRow_mem_fibre hDu hgram
  have hdet' := normalizeFirstRow_det_ne_zero hDu hdet
  rcases infinite_row_fibre_trichotomy hinf hmem hdet' with
    hfour | hneg | hopp
  · exact Or.inl ((normalizeFirstRow_isHadamard3_iff hDu).mp hfour)
  · right; left
    rw [rowTau_normalizeFirstRow hDu] at hneg
    exact hneg
  · right; right
    exact htwo H hH
      (normalizedBottomRight_oppositeRow_hasHadamardTwoByTwo hH hopp)

theorem bottomLeft_infinite_column_gram_fibre_outcome
    (htwo : TwoByTwoKarlssonCriterion IsKarlsson)
    {H : Mat6} (hH : IsHadamard H) {G : Mat3}
    (hgram : Matrix.conjTranspose (Matrix.toBlocks₂₁ H) *
      Matrix.toBlocks₂₁ H = G)
    (hinf : (normalizedColumnGramFibre G).Infinite)
    (hdet : (Matrix.toBlocks₂₁ H).det ≠ 0) :
    ColumnFibreOutcome IsKarlsson H (Matrix.toBlocks₂₁ H) := by
  let C := Matrix.toBlocks₂₁ H
  have hCu := (hadamard_blocks_entrywiseUnit hH).2.2.1
  have hmem := normalizeFirstColumn_mem_fibre hCu hgram
  have hdet' := normalizeFirstColumn_det_ne_zero hCu hdet
  rcases infinite_column_fibre_trichotomy hinf hmem hdet' with
    hfour | hneg | hopp
  · exact Or.inl ((normalizeFirstColumn_isHadamard3_iff hCu).mp hfour)
  · right; left
    rw [columnTau_normalizeFirstColumn_re hCu] at hneg
    exact hneg
  · right; right
    exact htwo H hH
      (normalizedBottomLeft_oppositeColumn_hasHadamardTwoByTwo hH hopp)

theorem topLeft_infinite_column_gram_fibre_outcome
    (htwo : TwoByTwoKarlssonCriterion IsKarlsson)
    {H : Mat6} (hH : IsHadamard H) {G : Mat3}
    (hgram : Matrix.conjTranspose (Matrix.toBlocks₁₁ H) *
      Matrix.toBlocks₁₁ H = G)
    (hinf : (normalizedColumnGramFibre G).Infinite)
    (hdet : (Matrix.toBlocks₁₁ H).det ≠ 0) :
    ColumnFibreOutcome IsKarlsson H (Matrix.toBlocks₁₁ H) := by
  let E := Matrix.toBlocks₁₁ H
  have hEu := (hadamard_blocks_entrywiseUnit hH).1
  have hmem := normalizeFirstColumn_mem_fibre hEu hgram
  have hdet' := normalizeFirstColumn_det_ne_zero hEu hdet
  rcases infinite_column_fibre_trichotomy hinf hmem hdet' with
    hfour | hneg | hopp
  · exact Or.inl ((normalizeFirstColumn_isHadamard3_iff hEu).mp hfour)
  · right; left
    rw [columnTau_normalizeFirstColumn_re hEu] at hneg
    exact hneg
  · right; right
    exact htwo H hH
      (normalizedTopLeft_oppositeColumn_hasHadamardTwoByTwo hH hopp)

end Hadamard6
