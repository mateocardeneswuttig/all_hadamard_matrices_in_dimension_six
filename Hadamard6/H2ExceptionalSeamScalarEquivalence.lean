import Hadamard6.H2ExceptionalSeamCommonEquivalence

/-!
# Scalar intrinsic cores are affine-Fourier

When the intrinsic Hermitian involution is scalar, the two core matrices are
`ωF₂` and `ω²F₂`.  The unit central blocks force either the two left
phases or the two right phases to be signs.  Pair swaps then expose the
affine-Fourier matrix directly.
-/

namespace Hadamard6

noncomputable section

/-- Swap the two members of the first tail pair. -/
def h2SwapFirstTailPair : Equiv.Perm I6 :=
  Equiv.swap h2Tail₀ h2Tail₁

private theorem h2_scalar_core_entries
    {K : Mat6} (h : H2BlockNormalizedPresentation K)
    {omega : ℂ}
    (hA : h2ParameterA K = omega • karlssonF2)
    (hB : h2ParameterB K = omega ^ 2 • karlssonF2) :
    (∀ i j : I2,
      karlssonBlockProduct (h2Z₃ K) (omega • karlssonF2)
          (h2Z₁ K) i j =
        K (h2TailPairFirst i) (h2TailPairFirst j)) ∧
    (∀ i j : I2,
      karlssonBlockProduct (h2Z₃ K) (omega ^ 2 • karlssonF2)
          (h2Z₂ K) i j =
        K (h2TailPairFirst i) (h2TailPairSecond j)) ∧
    (∀ i j : I2,
      karlssonBlockProduct (h2Z₄ K) (omega ^ 2 • karlssonF2)
          (h2Z₁ K) i j =
        K (h2TailPairSecond i) (h2TailPairFirst j)) ∧
    (∀ i j : I2,
      karlssonBlockProduct (h2Z₄ K) (omega • karlssonF2)
          (h2Z₂ K) i j =
        K (h2TailPairSecond i) (h2TailPairSecond j)) := by
  have hAeq := h2CoreA_reconstruct h.canonical
  have hBeq := h2CoreB_reconstruct h.canonical
  have hCeq := h2CoreC_reconstruct h.canonical
  have hDeq := h2CoreD_reconstruct h.canonical
  rw [hA] at hAeq
  rw [hB] at hBeq
  rw [h2ParameterC_eq_h2ParameterB h.canonical, hB] at hCeq
  rw [h2ParameterD_eq_h2ParameterA h.canonical, hA] at hDeq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    simpa [h2CoreA] using congrArg (fun M : Mat2 ↦ M i j) hAeq
  · intro i j
    simpa [h2CoreB] using congrArg (fun M : Mat2 ↦ M i j) hBeq
  · intro i j
    simpa [h2CoreC] using congrArg (fun M : Mat2 ↦ M i j) hCeq
  · intro i j
    simpa [h2CoreD] using congrArg (fun M : Mat2 ↦ M i j) hDeq

theorem h2_scalar_left_plus_plus_eq_affine
    {K : Mat6} (h : H2BlockNormalizedPresentation K)
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega)
    (hA : h2ParameterA K = omega • karlssonF2)
    (hB : h2ParameterB K = omega ^ 2 • karlssonF2)
    (hz₃ : h2Z₃ K = 1) (hz₄ : h2Z₄ K = 1) :
    K = affineFourierMatrix omega (h2Z₁ K) (h2Z₂ K) := by
  rcases h2_scalar_core_entries h hA hB with
    ⟨hAe, hBe, hCe, hDe⟩
  have hA00 := (hAe (0 : I2) (0 : I2)).symm
  have hA01 := (hAe (0 : I2) (1 : I2)).symm
  have hA10 := (hAe (1 : I2) (0 : I2)).symm
  have hA11 := (hAe (1 : I2) (1 : I2)).symm
  have hB00 := (hBe (0 : I2) (0 : I2)).symm
  have hB01 := (hBe (0 : I2) (1 : I2)).symm
  have hB10 := (hBe (1 : I2) (0 : I2)).symm
  have hB11 := (hBe (1 : I2) (1 : I2)).symm
  have hC00 := (hCe (0 : I2) (0 : I2)).symm
  have hC01 := (hCe (0 : I2) (1 : I2)).symm
  have hC10 := (hCe (1 : I2) (0 : I2)).symm
  have hC11 := (hCe (1 : I2) (1 : I2)).symm
  have hD00 := (hDe (0 : I2) (0 : I2)).symm
  have hD01 := (hDe (0 : I2) (1 : I2)).symm
  have hD10 := (hDe (1 : I2) (0 : I2)).symm
  have hD11raw := (hDe (1 : I2) (1 : I2)).symm
  simp only [h2TailPairFirst_zero, h2TailPairFirst_one,
    h2TailPairSecond_zero, h2TailPairSecond_one,
    h2Tail₀, h2Tail₁, h2Tail₂, h2Tail₃] at hA00 hA01 hA10 hA11
  simp only [h2TailPairFirst_zero, h2TailPairFirst_one,
    h2TailPairSecond_zero, h2TailPairSecond_one,
    h2Tail₀, h2Tail₁, h2Tail₂, h2Tail₃] at hB00 hB01 hB10 hB11
  simp only [h2TailPairFirst_zero, h2TailPairFirst_one,
    h2TailPairSecond_zero, h2TailPairSecond_one,
    h2Tail₀, h2Tail₁, h2Tail₂, h2Tail₃] at hC00 hC01 hC10 hC11
  simp only [h2TailPairFirst_zero, h2TailPairFirst_one,
    h2TailPairSecond_zero, h2TailPairSecond_one,
    h2Tail₀, h2Tail₁, h2Tail₂, h2Tail₃] at hD00 hD01 hD10 hD11raw
  have hrow₁ : K (Sum.inl 1) (Sum.inr 0) =
      -K (Sum.inl 1) (Sum.inl 2) := by
    simpa [h2Tail₀, h2Tail₁] using h.canonical.row_pair₁
  have hrow₂ : K (Sum.inl 1) (Sum.inr 2) =
      -K (Sum.inl 1) (Sum.inr 1) := by
    simpa [h2Tail₂, h2Tail₃] using h.canonical.row_pair₂
  have hcol₁ : K (Sum.inr 0) (Sum.inl 1) =
      -K (Sum.inl 2) (Sum.inl 1) := by
    simpa [h2Tail₀, h2Tail₁] using h.canonical.column_pair₁
  have hcol₂ : K (Sum.inr 2) (Sum.inl 1) =
      -K (Sum.inr 1) (Sum.inl 1) := by
    simpa [h2Tail₂, h2Tail₃] using h.canonical.column_pair₂
  have hsum : 1 + omega + omega ^ 2 = 0 := by
    linear_combination homega.2
  have hz₃c : K (Sum.inl 2) (Sum.inl 1) = 1 := by
    simpa [h2Z₃, h2Tail₀] using hz₃
  have hz₄c : K (Sum.inr 1) (Sum.inl 1) = 1 := by
    simpa [h2Z₄, h2Tail₂] using hz₄
  have hD11 : K (Sum.inr 2) (Sum.inr 2) =
      -(omega * K (Sum.inl 1) (Sum.inr 1)) := by
    calc
      K (Sum.inr 2) (Sum.inr 2) =
          -(2⁻¹ * ((omega + omega) * K (Sum.inl 1) (Sum.inr 1))) := by
        simpa [h2TailPairSecond, h2Tail₂, h2Tail₃,
          karlssonBlockProduct, karlssonZLeft, karlssonZRight,
          karlssonF2, Matrix.mul_apply, Fin.sum_univ_two,
          h2Z₂, hz₄] using (hDe 1 1).symm
      _ = -(omega * K (Sum.inl 1) (Sum.inr 1)) := by ring
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [affineFourierMatrix, h.canonical.dephased.1,
      h.canonical.dephased.2, h.canonical.leading_neg_one,
      h2TailPairFirst, h2TailPairSecond, h2Tail₀, h2Tail₁,
      h2Tail₂, h2Tail₃,
      hA00, hA01, hA10, hA11, hB00, hB01, hB10, hB11,
      hC00, hC01, hC10, hC11, hD00, hD01, hD10, hD11raw,
      karlssonBlockProduct, karlssonZLeft, karlssonZRight,
      karlssonF2, Matrix.mul_apply, Fin.sum_univ_two,
      h2Z₁, h2Z₂, h2Z₃, h2Z₄, hz₃, hz₄,
      hz₃c, hz₄c, hrow₁, hrow₂, hcol₁, hcol₂, hD11] <;>
    try ring_nf

def scalarLeftNormalizationPermutation (z₃ z₄ : ℂ) : Equiv.Perm I6 :=
  if z₃ = 1 then
    if z₄ = 1 then Equiv.refl I6 else h2SwapSecondTailPair
  else
    if z₄ = 1 then h2SwapFirstTailPair
    else h2SwapFirstTailPair.trans h2SwapSecondTailPair

/-- Both left phases being signs is exactly the row-pair ambiguity of the
affine-Fourier normal form. -/
theorem h2_scalar_left_signs_reindex_eq_affine
    {K : Mat6} (h : H2BlockNormalizedPresentation K)
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega)
    (hA : h2ParameterA K = omega • karlssonF2)
    (hB : h2ParameterB K = omega ^ 2 • karlssonF2)
    (hz₃ : h2Z₃ K ^ 2 = 1) (hz₄ : h2Z₄ K ^ 2 = 1) :
    reindexMatrix
        (scalarLeftNormalizationPermutation (h2Z₃ K) (h2Z₄ K))
        (Equiv.refl I6) K =
      affineFourierMatrix omega (h2Z₁ K) (h2Z₂ K) := by
  rcases h2_scalar_core_entries h hA hB with
    ⟨hAe, hBe, hCe, hDe⟩
  have hA00 := (hAe (0 : I2) (0 : I2)).symm
  have hA01 := (hAe (0 : I2) (1 : I2)).symm
  have hA10 := (hAe (1 : I2) (0 : I2)).symm
  have hA11 := (hAe (1 : I2) (1 : I2)).symm
  have hB00 := (hBe (0 : I2) (0 : I2)).symm
  have hB01 := (hBe (0 : I2) (1 : I2)).symm
  have hB10 := (hBe (1 : I2) (0 : I2)).symm
  have hB11 := (hBe (1 : I2) (1 : I2)).symm
  have hC00 := (hCe (0 : I2) (0 : I2)).symm
  have hC01 := (hCe (0 : I2) (1 : I2)).symm
  have hC10 := (hCe (1 : I2) (0 : I2)).symm
  have hC11 := (hCe (1 : I2) (1 : I2)).symm
  have hD00 := (hDe (0 : I2) (0 : I2)).symm
  have hD01 := (hDe (0 : I2) (1 : I2)).symm
  have hD10 := (hDe (1 : I2) (0 : I2)).symm
  have hD11 := (hDe (1 : I2) (1 : I2)).symm
  simp only [h2TailPairFirst_zero, h2TailPairFirst_one,
    h2TailPairSecond_zero, h2TailPairSecond_one,
    h2Tail₀, h2Tail₁, h2Tail₂, h2Tail₃] at hA00 hA01 hA10 hA11
  simp only [h2TailPairFirst_zero, h2TailPairFirst_one,
    h2TailPairSecond_zero, h2TailPairSecond_one,
    h2Tail₀, h2Tail₁, h2Tail₂, h2Tail₃] at hB00 hB01 hB10 hB11
  simp only [h2TailPairFirst_zero, h2TailPairFirst_one,
    h2TailPairSecond_zero, h2TailPairSecond_one,
    h2Tail₀, h2Tail₁, h2Tail₂, h2Tail₃] at hC00 hC01 hC10 hC11
  simp only [h2TailPairFirst_zero, h2TailPairFirst_one,
    h2TailPairSecond_zero, h2TailPairSecond_one,
    h2Tail₀, h2Tail₁, h2Tail₂, h2Tail₃] at hD00 hD01 hD10 hD11
  have hrow₁ : K (Sum.inl 1) (Sum.inr 0) =
      -K (Sum.inl 1) (Sum.inl 2) := by
    simpa [h2Tail₀, h2Tail₁] using h.canonical.row_pair₁
  have hrow₂ : K (Sum.inl 1) (Sum.inr 2) =
      -K (Sum.inl 1) (Sum.inr 1) := by
    simpa [h2Tail₂, h2Tail₃] using h.canonical.row_pair₂
  have hcol₁ : K (Sum.inr 0) (Sum.inl 1) =
      -K (Sum.inl 2) (Sum.inl 1) := by
    simpa [h2Tail₀, h2Tail₁] using h.canonical.column_pair₁
  have hcol₂ : K (Sum.inr 2) (Sum.inl 1) =
      -K (Sum.inr 1) (Sum.inl 1) := by
    simpa [h2Tail₂, h2Tail₃] using h.canonical.column_pair₂
  have hsum : 1 + omega + omega ^ 2 = 0 := by
    linear_combination homega.2
  have hneg : (-1 : ℂ) ≠ 1 := by norm_num
  rcases (sq_eq_one_iff).mp hz₃ with hz₃' | hz₃' <;>
    rcases (sq_eq_one_iff).mp hz₄ with hz₄' | hz₄'
  all_goals
    have hz₃c := hz₃'
    have hz₄c := hz₄'
    simp only [h2Z₃, h2Tail₀] at hz₃c
    simp only [h2Z₄, h2Tail₂] at hz₄c
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [scalarLeftNormalizationPermutation, reindexMatrix,
        hz₃', hz₄', affineFourierMatrix, h.canonical.dephased.1,
        h.canonical.dephased.2, h.canonical.leading_neg_one,
        h2SwapFirstTailPair, h2SwapSecondTailPair, Equiv.swap_apply_def,
        h2TailPairFirst, h2TailPairSecond, h2Tail₀, h2Tail₁,
        h2Tail₂, h2Tail₃,
        hA00, hA01, hA10, hA11, hB00, hB01, hB10, hB11,
        hC00, hC01, hC10, hC11, hD00, hD01, hD10, hD11,
        karlssonBlockProduct, karlssonZLeft, karlssonZRight,
        karlssonF2, Matrix.mul_apply, Fin.sum_univ_two,
        h2Z₁, h2Z₂, h2Z₃, h2Z₄, hrow₁, hrow₂,
        hcol₁, hcol₂, hneg, hz₃c, hz₄c] <;>
      try ring_nf

private theorem equivalent_transpose_local {H K : Mat6}
    (hHK : Equivalent H K) : Equivalent H.transpose K.transpose := by
  rcases hHK with ⟨σ, τ, r, c, hr, hc, hpres⟩
  refine ⟨τ, σ, c, r, hc, hr, ?_⟩
  intro i j
  simp only [Matrix.transpose_apply]
  rw [hpres]
  ring

/-- Scalar intrinsic cores lie on the affine-Fourier seam. -/
theorem h2_scalar_core_isAffineFourierSeam
    {K : Mat6} (h : H2BlockNormalizedPresentation K)
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega)
    (hA : h2ParameterA K = omega • karlssonF2)
    (hB : h2ParameterB K = omega ^ 2 • karlssonF2) :
    IsAffineFourierSeam K := by
  rcases h2_scalar_core_entries h hA hB with
    ⟨hAe, hBe, hCe, hDe⟩
  have hAunit : Complex.normSq
      (karlssonBlockProduct (h2Z₃ K) (omega • karlssonF2)
        (h2Z₁ K) 0 0) = 1 := by
    rw [hAe 0 0]
    exact h.coreBlocks.1.1 0 0
  have hBunit : Complex.normSq
      (karlssonBlockProduct (h2Z₃ K) (omega ^ 2 • karlssonF2)
        (h2Z₂ K) 0 0) = 1 := by
    rw [hBe 0 0]
    exact h.coreBlocks.2.1.1 0 0
  have hCunit : Complex.normSq
      (karlssonBlockProduct (h2Z₄ K) (omega ^ 2 • karlssonF2)
        (h2Z₁ K) 0 0) = 1 := by
    rw [hCe 0 0]
    exact h.coreBlocks.2.2.1.1 0 0
  have hDunit : Complex.normSq
      (karlssonBlockProduct (h2Z₄ K) (omega • karlssonF2)
        (h2Z₂ K) 0 0) = 1 := by
    rw [hDe 0 0]
    exact h.coreBlocks.2.2.2.1 0 0
  have homegaSq : Complex.normSq (omega ^ 2) = 1 :=
    primitiveCubicPhase_sq_norm homega
  have hAalt := scalarFourierBlock_unit_forces_square_one
    homega.1 h.canonical.z₃_unit h.canonical.z₁_unit hAunit
  have hBalt := scalarFourierBlock_unit_forces_square_one
    homegaSq h.canonical.z₃_unit h.canonical.z₂_unit hBunit
  have hCalt := scalarFourierBlock_unit_forces_square_one
    homegaSq h.canonical.z₄_unit h.canonical.z₁_unit hCunit
  have hDalt := scalarFourierBlock_unit_forces_square_one
    homega.1 h.canonical.z₄_unit h.canonical.z₂_unit hDunit
  have hpair :
      (h2Z₃ K ^ 2 = 1 ∧ h2Z₄ K ^ 2 = 1) ∨
      (h2Z₁ K ^ 2 = 1 ∧ h2Z₂ K ^ 2 = 1) := by
    tauto
  rcases hpair with hleft | hright
  · have heq := h2_scalar_left_signs_reindex_eq_affine
      h homega hA hB hleft.1 hleft.2
    have hperm := equivalent_reindexMatrix
      (scalarLeftNormalizationPermutation (h2Z₃ K) (h2Z₄ K))
      (Equiv.refl I6) K
    rw [heq] at hperm
    exact ⟨omega, h2Z₁ K, h2Z₂ K, homega,
      h.canonical.z₁_unit, h.canonical.z₂_unit, Or.inl hperm⟩
  · have hT : H2BlockNormalizedPresentation K.transpose := by
      have ht := h2BlockNormalizedPresentation_of_transpose
        (K := K.transpose) (by simpa using h)
      simpa using ht
    have hAT :
        h2ParameterA K.transpose = omega • karlssonF2 := by
      rw [h2ParameterA_transpose, hA]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [karlssonF2]
    have hBT :
        h2ParameterB K.transpose = omega ^ 2 • karlssonF2 := by
      rw [h2ParameterB_transpose,
        h2ParameterC_eq_h2ParameterB h.canonical, hB]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [karlssonF2]
    have hleftT :
        h2Z₃ K.transpose ^ 2 = 1 ∧ h2Z₄ K.transpose ^ 2 = 1 := by
      simpa [h2Z₁, h2Z₂, h2Z₃, h2Z₄] using hright
    have heqT := h2_scalar_left_signs_reindex_eq_affine
      hT homega hAT hBT hleftT.1 hleftT.2
    have hpermT := equivalent_reindexMatrix
      (scalarLeftNormalizationPermutation
        (h2Z₃ K.transpose) (h2Z₄ K.transpose))
      (Equiv.refl I6) K.transpose
    rw [heqT] at hpermT
    have htrans := equivalent_transpose_local hpermT
    have htarget : Equivalent K
        (affineFourierMatrix omega (h2Z₃ K) (h2Z₄ K)).transpose := by
      simpa [h2Z₁, h2Z₂, h2Z₃, h2Z₄] using htrans
    exact ⟨omega, h2Z₃ K, h2Z₄ K, homega,
      h.canonical.z₃_unit, h.canonical.z₄_unit, Or.inr htarget⟩

end

end Hadamard6
