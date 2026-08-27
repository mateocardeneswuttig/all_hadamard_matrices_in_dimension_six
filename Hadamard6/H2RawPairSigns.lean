import Hadamard6.KarlssonGlobalModel

/-!
# Sign changes of the four raw Karlsson phase pairs

Negating one phase reverses the corresponding order-two row or column pair.
We verify the four elementary swaps in the mixed block chart and then
transport them to raw coordinates. No parameter guard is used.
-/

namespace Hadamard6

noncomputable section

def karlssonMixedSwapFirstPair : Equiv.Perm I6 :=
  Equiv.swap (Sum.inl 1) (Sum.inl 2)

def karlssonMixedSwapSecondPair : Equiv.Perm I6 :=
  Equiv.swap (Sum.inr 1) (Sum.inr 2)

set_option maxHeartbeats 1000000 in
-- The proof checks the 36 entries of one explicit pair swap.
private theorem equivalent_karlssonMixed_neg_z₁
    (t : ℝ) (p z₁ z₂ z₃ z₄ : ℂ) :
    Equivalent (karlssonMixedChartMatrix t p z₁ z₂ z₃ z₄)
      (karlssonMixedChartMatrix t p (-z₁) z₂ z₃ z₄) := by
  refine ⟨Equiv.refl I6, karlssonMixedSwapFirstPair,
    (fun _ ↦ 1), (fun _ ↦ 1),
    (by intro i; norm_num), (by intro j; norm_num), ?_⟩
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [karlssonMixedSwapFirstPair, karlssonMixedChartMatrix,
      karlssonMixedE, karlssonMixedB, karlssonMixedC, karlssonMixedD,
      mixedLeadingBlock, mixedHorizontalBlock, karlssonBlockProduct,
      karlssonZLeft, karlssonZRight, Equiv.swap_apply_def,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

set_option maxHeartbeats 1000000 in
-- The proof checks the 36 entries of one explicit pair swap.
private theorem equivalent_karlssonMixed_neg_z₂
    (t : ℝ) (p z₁ z₂ z₃ z₄ : ℂ) :
    Equivalent (karlssonMixedChartMatrix t p z₁ z₂ z₃ z₄)
      (karlssonMixedChartMatrix t p z₁ (-z₂) z₃ z₄) := by
  refine ⟨Equiv.refl I6, karlssonMixedSwapSecondPair,
    (fun _ ↦ 1), (fun _ ↦ 1),
    (by intro i; norm_num), (by intro j; norm_num), ?_⟩
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [karlssonMixedSwapSecondPair, karlssonMixedChartMatrix,
      karlssonMixedE, karlssonMixedB, karlssonMixedC, karlssonMixedD,
      mixedLeadingBlock, mixedHorizontalBlock, karlssonBlockProduct,
      karlssonZLeft, karlssonZRight, Equiv.swap_apply_def,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

set_option maxHeartbeats 1000000 in
-- The proof checks the 36 entries of one explicit pair swap.
private theorem equivalent_karlssonMixed_neg_z₃
    (t : ℝ) (p z₁ z₂ z₃ z₄ : ℂ) :
    Equivalent (karlssonMixedChartMatrix t p z₁ z₂ z₃ z₄)
      (karlssonMixedChartMatrix t p z₁ z₂ (-z₃) z₄) := by
  refine ⟨karlssonMixedSwapFirstPair, Equiv.refl I6,
    (fun _ ↦ 1), (fun _ ↦ 1),
    (by intro i; norm_num), (by intro j; norm_num), ?_⟩
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [karlssonMixedSwapFirstPair, karlssonMixedChartMatrix,
      karlssonMixedE, karlssonMixedB, karlssonMixedC, karlssonMixedD,
      mixedLeadingBlock, mixedHorizontalBlock, karlssonBlockProduct,
      karlssonZLeft, karlssonZRight, Equiv.swap_apply_def,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

set_option maxHeartbeats 1000000 in
-- The proof checks the 36 entries of one explicit pair swap.
private theorem equivalent_karlssonMixed_neg_z₄
    (t : ℝ) (p z₁ z₂ z₃ z₄ : ℂ) :
    Equivalent (karlssonMixedChartMatrix t p z₁ z₂ z₃ z₄)
      (karlssonMixedChartMatrix t p z₁ z₂ z₃ (-z₄)) := by
  refine ⟨karlssonMixedSwapSecondPair, Equiv.refl I6,
    (fun _ ↦ 1), (fun _ ↦ 1),
    (by intro i; norm_num), (by intro j; norm_num), ?_⟩
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [karlssonMixedSwapSecondPair, karlssonMixedChartMatrix,
      karlssonMixedE, karlssonMixedB, karlssonMixedC, karlssonMixedD,
      mixedLeadingBlock, mixedHorizontalBlock, karlssonBlockProduct,
      karlssonZLeft, karlssonZRight, Equiv.swap_apply_def,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem raw_sign_from_mixed
    {t : ℝ} {p z₁ z₂ z₃ z₄ w₁ w₂ w₃ w₄ : ℂ}
    (hmixed : Equivalent
      (karlssonMixedChartMatrix t p z₁ z₂ z₃ z₄)
      (karlssonMixedChartMatrix t p w₁ w₂ w₃ w₄)) :
    Equivalent (karlssonRawMatrix t p z₁ z₂ z₃ z₄)
      (karlssonRawMatrix t p w₁ w₂ w₃ w₄) := by
  exact equivalent_trans
    (equivalent_karlssonMixedChartMatrix t p z₁ z₂ z₃ z₄)
    (equivalent_trans hmixed
      (equivalent_symm
        (equivalent_karlssonMixedChartMatrix t p w₁ w₂ w₃ w₄)))

theorem equivalent_karlssonRawMatrix_neg_z₁
    (t : ℝ) (p z₁ z₂ z₃ z₄ : ℂ) :
    Equivalent (karlssonRawMatrix t p z₁ z₂ z₃ z₄)
      (karlssonRawMatrix t p (-z₁) z₂ z₃ z₄) :=
  raw_sign_from_mixed
    (equivalent_karlssonMixed_neg_z₁ t p z₁ z₂ z₃ z₄)

theorem equivalent_karlssonRawMatrix_neg_z₂
    (t : ℝ) (p z₁ z₂ z₃ z₄ : ℂ) :
    Equivalent (karlssonRawMatrix t p z₁ z₂ z₃ z₄)
      (karlssonRawMatrix t p z₁ (-z₂) z₃ z₄) :=
  raw_sign_from_mixed
    (equivalent_karlssonMixed_neg_z₂ t p z₁ z₂ z₃ z₄)

theorem equivalent_karlssonRawMatrix_neg_z₃
    (t : ℝ) (p z₁ z₂ z₃ z₄ : ℂ) :
    Equivalent (karlssonRawMatrix t p z₁ z₂ z₃ z₄)
      (karlssonRawMatrix t p z₁ z₂ (-z₃) z₄) :=
  raw_sign_from_mixed
    (equivalent_karlssonMixed_neg_z₃ t p z₁ z₂ z₃ z₄)

theorem equivalent_karlssonRawMatrix_neg_z₄
    (t : ℝ) (p z₁ z₂ z₃ z₄ : ℂ) :
    Equivalent (karlssonRawMatrix t p z₁ z₂ z₃ z₄)
      (karlssonRawMatrix t p z₁ z₂ z₃ (-z₄)) :=
  raw_sign_from_mixed
    (equivalent_karlssonMixed_neg_z₄ t p z₁ z₂ z₃ z₄)

end

end Hadamard6
