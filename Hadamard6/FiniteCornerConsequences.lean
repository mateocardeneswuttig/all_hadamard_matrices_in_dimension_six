import Hadamard6.BlockCompletion
import Hadamard6.VanishingMinorReduction

/-!
# Finite-corner soundness and block invertibility

These are the two direct consequences used by the public classification and
the block-swap argument.
-/

namespace Hadamard6

variable {IsKarlsson : Mat6 → Prop}

/-- Every retained completion is Hadamard. -/
theorem retained_completion_isHadamard
    {p : CornerData} {B C : Mat3}
    (h : Retained p.matrix B C) :
    IsHadamard (completion p.matrix B C) :=
  ⟨retained_completion_entrywiseUnit h,
    retained_completion_rowGram h⟩

/-- Every matrix represented by the finite-corner atlas is Hadamard. -/
theorem inFiniteCornerAtlas_isHadamard {H : Mat6}
    (hH : InFiniteCornerAtlas H) : IsHadamard H := by
  rcases hH with ⟨p, B, C, hret, heq⟩
  exact (equivalent_isHadamard_iff heq).2
    (retained_completion_isHadamard hret)

/-- Outside the intrinsic Karlsson sector, all four blocks of the fixed
`3 + 3` decomposition are invertible. -/
theorem all_four_blocks_det_ne_zero
    (htwo : TwoByTwoKarlssonCriterion IsKarlsson)
    {H : Mat6} (hH : IsHadamard H) (hK : ¬ IsKarlsson H) :
    Matrix.det (Matrix.toBlocks₁₁ H) ≠ 0 ∧
    Matrix.det (Matrix.toBlocks₁₂ H) ≠ 0 ∧
    Matrix.det (Matrix.toBlocks₂₁ H) ≠ 0 ∧
    Matrix.det (Matrix.toBlocks₂₂ H) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    exact hK (htwo H hH
      (singular_topLeft_hasHadamardTwoByTwo hH hzero))
  · intro hzero
    exact hK (htwo H hH
      (singular_topRight_hasHadamardTwoByTwo hH hzero))
  · intro hzero
    exact hK (htwo H hH
      (singular_bottomLeft_hasHadamardTwoByTwo hH hzero))
  · intro hzero
    exact hK (htwo H hH
      (singular_bottomRight_hasHadamardTwoByTwo hH hzero))

end Hadamard6
