import Hadamard6.FourierSeamCertificateExceptional

namespace Hadamard6

noncomputable section

/-! A structural symmetry used only for the two projective boundary lines. -/

def swapBlockNoninitialRows (H : Mat6) : Mat6 :=
  fun i j ↦ H (Sum.map swapNoninitialIndex swapNoninitialIndex i) j

def swapNoninitialColumns (X : Mat3) : Mat3 :=
  fun i j ↦ X i (swapNoninitialIndex j)

theorem toBlocks₁₁_swapBlockNoninitialRows (H : Mat6) :
    Matrix.toBlocks₁₁ (swapBlockNoninitialRows H) =
      swapNoninitialRows (Matrix.toBlocks₁₁ H) := by
  rfl

theorem toBlocks₁₂_swapBlockNoninitialRows (H : Mat6) :
    Matrix.toBlocks₁₂ (swapBlockNoninitialRows H) =
      swapNoninitialRows (Matrix.toBlocks₁₂ H) := by
  rfl

theorem toBlocks₂₁_swapBlockNoninitialRows (H : Mat6) :
    Matrix.toBlocks₂₁ (swapBlockNoninitialRows H) =
      swapNoninitialRows (Matrix.toBlocks₂₁ H) := by
  rfl

theorem swapNoninitialRows_transpose (X : Mat3) :
    (swapNoninitialRows X).transpose =
      swapNoninitialColumns X.transpose := by
  rfl

theorem swapNoninitialRows_swapNoninitialColumns (X : Mat3) :
    swapNoninitialRows (swapNoninitialColumns X) =
      swapNoninitialColumns (swapNoninitialRows X) := by
  rfl

theorem swapNoninitialColumns_rowGram (X : Mat3) :
    swapNoninitialColumns X *
        Matrix.conjTranspose (swapNoninitialColumns X) =
      X * Matrix.conjTranspose X := by
  ext i j
  simp [swapNoninitialColumns, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_three]
  ring

theorem rowEndpoint0_swapNoninitialColumns (X : Mat3) :
    rowEndpoint0 (swapNoninitialColumns X) = rowEndpoint0 X := by
  simp [rowEndpoint0, swapNoninitialColumns_rowGram]

theorem rowEndpoint3_swapNoninitialColumns (X : Mat3) :
    rowEndpoint3 (swapNoninitialColumns X) = rowEndpoint3 X := by
  simp [rowEndpoint3, swapNoninitialColumns_rowGram]

theorem leadingCertificate_swapBlockNoninitialRows {H : Mat6}
    (h : LeadingFiniteCornerCertificate H) :
    LeadingFiniteCornerCertificate (swapBlockNoninitialRows H) := by
  refine {
    detE := ?_, detB := ?_, detC := ?_,
    B_endpoint0 := ?_, B_endpoint3 := ?_,
    B_swapped_endpoint0 := ?_, B_swapped_endpoint3 := ?_,
    C_endpoint0 := ?_, C_endpoint3 := ?_,
    C_swapped_endpoint0 := ?_, C_swapped_endpoint3 := ?_ }
  · rw [toBlocks₁₁_swapBlockNoninitialRows]
    exact swapNoninitialRows_det_ne_zero h.detE
  · rw [toBlocks₁₂_swapBlockNoninitialRows]
    exact swapNoninitialRows_det_ne_zero h.detB
  · rw [toBlocks₂₁_swapBlockNoninitialRows]
    exact swapNoninitialRows_det_ne_zero h.detC
  · rw [toBlocks₁₂_swapBlockNoninitialRows]
    exact h.B_swapped_endpoint0
  · rw [toBlocks₁₂_swapBlockNoninitialRows]
    exact h.B_swapped_endpoint3
  · rw [toBlocks₁₂_swapBlockNoninitialRows]
    simpa [swapNoninitialRows_involutive] using h.B_endpoint0
  · rw [toBlocks₁₂_swapBlockNoninitialRows]
    simpa [swapNoninitialRows_involutive] using h.B_endpoint3
  · rw [toBlocks₂₁_swapBlockNoninitialRows]
    simpa [swapNoninitialRows_transpose,
      rowEndpoint0_swapNoninitialColumns] using
      h.C_endpoint0
  · rw [toBlocks₂₁_swapBlockNoninitialRows]
    simpa [swapNoninitialRows_transpose,
      rowEndpoint3_swapNoninitialColumns] using
      h.C_endpoint3
  · rw [toBlocks₂₁_swapBlockNoninitialRows]
    simpa [swapNoninitialRows_transpose,
      swapNoninitialRows_swapNoninitialColumns,
      rowEndpoint0_swapNoninitialColumns] using h.C_swapped_endpoint0
  · rw [toBlocks₂₁_swapBlockNoninitialRows]
    simpa [swapNoninitialRows_transpose,
      swapNoninitialRows_swapNoninitialColumns,
      rowEndpoint3_swapNoninitialColumns] using h.C_swapped_endpoint3

theorem seamCorner20_eq_swap_first {z₁ z₂ : ℂ}
    (_hz₁ : Complex.normSq z₁ = 1) (_hz₂ : Complex.normSq z₂ = 1) :
    seamCornerChart (2 : I3) (0 : I2)
        (affineFourierMatrix standardOmega z₁ z₂) =
      swapBlockNoninitialRows
        (firstSeamChart standardOmega
          (standardOmega ^ 2 * z₁) (standardOmega * z₂)) := by
  change dephase (reindexMatrix seamRows025 seamColumns024
      (affineFourierMatrix standardOmega z₁ z₂)) =
    swapBlockNoninitialRows
      (firstSeamChart standardOmega
        (standardOmega ^ 2 * z₁) (standardOmega * z₂))
  rcases seamRows025_order with ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩
  rcases seamColumns024_order with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have homega := standardOmega_isPrimitiveCubicPhase
  have hpow4 : standardOmega ^ 4 = standardOmega := by
    calc
      standardOmega ^ 4 = standardOmega * standardOmega ^ 3 := by ring
      _ = standardOmega := by rw [primitiveCubicPhase_cube homega, mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [dephase, phaseTransform, dephaseRowFactor,
      dephaseColumnFactor, reindexMatrix, hr0, hr1, hr2, hr3, hr4, hr5,
      hc0, hc1, hc2, hc3, hc4, hc5, affineFourierMatrix,
      swapBlockNoninitialRows, firstSeamChart] <;>
    ring_nf <;>
    simp [hpow4, primitiveCubicPhase_cube homega]

theorem corner20_witness_of_first_transformed
    {z₁ z₂ : ℂ} (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1)
    (hfirst : leadingFiniteCornerWitnessProduct
      (firstSeamChart standardOmega
        (standardOmega ^ 2 * z₁) (standardOmega * z₂)) ≠ 0) :
    leadingFiniteCornerWitnessProduct
      (seamCornerChart (2 : I3) (0 : I2)
        (affineFourierMatrix standardOmega z₁ z₂)) ≠ 0 := by
  have hcertificate : LeadingFiniteCornerCertificate
      (firstSeamChart standardOmega
        (standardOmega ^ 2 * z₁) (standardOmega * z₂)) :=
    leadingFiniteCornerCertificate_iff_witnessProduct_ne_zero.2 hfirst
  rw [seamCorner20_eq_swap_first hz₁ hz₂]
  exact leadingFiniteCornerCertificate_iff_witnessProduct_ne_zero.1
    (leadingCertificate_swapBlockNoninitialRows hcertificate)

theorem transformed_first_nonzero_of_z1_neg_one
    {z₂ : ℂ} (hz₂ : Complex.normSq z₂ = 1)
    (hspecial : z₂ ≠ -(standardOmega ^ 2)) :
    leadingFiniteCornerWitnessProduct
      (firstSeamChart standardOmega
        (standardOmega ^ 2 * (-1)) (standardOmega * z₂)) ≠ 0 := by
  have homega := standardOmega_isPrimitiveCubicPhase
  have hmul : standardOmega ^ 2 * standardOmega = 1 := by
    calc
      standardOmega ^ 2 * standardOmega = standardOmega ^ 3 := by ring
      _ = 1 := primitiveCubicPhase_cube homega
  have ht₂norm : Complex.normSq (standardOmega * z₂) = 1 := by
    rw [Complex.normSq_mul, homega.1, hz₂]
    norm_num
  have ht₂m : standardOmega * z₂ ≠ -1 := by
    intro ht
    apply hspecial
    calc
      z₂ = 1 * z₂ := by ring
      _ = standardOmega ^ 2 * (standardOmega * z₂) := by rw [← mul_assoc, hmul]
      _ = -(standardOmega ^ 2) := by rw [ht]; ring
  rcases exists_seamCayley_of_normSq_one ht₂norm ht₂m with ⟨y, hy⟩
  rw [hy]
  intro hzero
  have hzero' : leadingFiniteCornerWitnessProduct
      (firstSeamChart standardOmega
        (seamCayley (s3 / 3)) (seamCayley y)) = 0 := by
    simpa [seamCayley_third_s3] using hzero
  have hexceptional := firstSeam_witness_zero_cases hzero'
  rcases hexceptional with h00 | hsns | hnss | hns3ns | hns3s3 | hss3
  · rcases h00 with ⟨hx, _⟩; nlinarith [s3_pos]
  · rcases hsns with ⟨hx, _⟩; nlinarith [s3_pos]
  · rcases hnss with ⟨hx, _⟩; nlinarith [s3_pos]
  · rcases hns3ns with ⟨hx, _⟩; nlinarith [s3_pos]
  · rcases hns3s3 with ⟨hx, _⟩; nlinarith [s3_pos]
  · rcases hss3 with ⟨hx, _⟩; nlinarith [s3_pos]

theorem transformed_first_nonzero_of_z2_neg_one
    {z₁ : ℂ} (hz₁ : Complex.normSq z₁ = 1)
    (hspecial : z₁ ≠ -standardOmega) :
    leadingFiniteCornerWitnessProduct
      (firstSeamChart standardOmega
        (standardOmega ^ 2 * z₁) (standardOmega * (-1))) ≠ 0 := by
  have homega := standardOmega_isPrimitiveCubicPhase
  have hmul : standardOmega * standardOmega ^ 2 = 1 := by
    calc
      standardOmega * standardOmega ^ 2 = standardOmega ^ 3 := by ring
      _ = 1 := primitiveCubicPhase_cube homega
  have ht₁norm : Complex.normSq (standardOmega ^ 2 * z₁) = 1 := by
    rw [Complex.normSq_mul, primitiveCubicPhase_sq_norm homega, hz₁]
    norm_num
  have ht₁m : standardOmega ^ 2 * z₁ ≠ -1 := by
    intro ht
    apply hspecial
    calc
      z₁ = 1 * z₁ := by ring
      _ = standardOmega * (standardOmega ^ 2 * z₁) := by rw [← mul_assoc, hmul]
      _ = -standardOmega := by rw [ht]; ring
  rcases exists_seamCayley_of_normSq_one ht₁norm ht₁m with ⟨x, hx⟩
  rw [hx]
  intro hzero
  have hzero' : leadingFiniteCornerWitnessProduct
      (firstSeamChart standardOmega
        (seamCayley x) (seamCayley (-s3 / 3))) = 0 := by
    simpa [seamCayley_neg_third_s3] using hzero
  have hexceptional := firstSeam_witness_zero_cases hzero'
  rcases hexceptional with h00 | hsns | hnss | hns3ns | hns3s3 | hss3
  · rcases h00 with ⟨_, hy⟩; nlinarith [s3_pos]
  · rcases hsns with ⟨_, hy⟩; nlinarith [s3_pos]
  · rcases hnss with ⟨_, hy⟩; nlinarith [s3_pos]
  · rcases hns3ns with ⟨_, hy⟩; nlinarith [s3_pos]
  · rcases hns3s3 with ⟨_, hy⟩; nlinarith [s3_pos]
  · rcases hss3 with ⟨_, hy⟩; nlinarith [s3_pos]

theorem standard_z1_neg_one_six_corner_certificate
    {z₂ : ℂ} (hz₂ : Complex.normSq z₂ = 1) :
    ∃ r : I3, ∃ c : I2,
      leadingFiniteCornerWitnessProduct
        (seamCornerChart r c
          (affineFourierMatrix standardOmega (-1) z₂)) ≠ 0 := by
  by_cases hspecial : z₂ = -(standardOmega ^ 2)
  · subst z₂
    exact ⟨1, 0, boundary_neg_one_neg_omega_sq_corner10⟩
  · refine ⟨2, 0, corner20_witness_of_first_transformed
      (by norm_num) hz₂ ?_⟩
    exact transformed_first_nonzero_of_z1_neg_one hz₂ hspecial

theorem standard_z2_neg_one_six_corner_certificate
    {z₁ : ℂ} (hz₁ : Complex.normSq z₁ = 1) :
    ∃ r : I3, ∃ c : I2,
      leadingFiniteCornerWitnessProduct
        (seamCornerChart r c
          (affineFourierMatrix standardOmega z₁ (-1))) ≠ 0 := by
  by_cases hspecial : z₁ = -standardOmega
  · subst z₁
    exact ⟨1, 0, boundary_neg_omega_neg_one_corner10⟩
  · refine ⟨2, 0, corner20_witness_of_first_transformed
      hz₁ (by norm_num) ?_⟩
    exact transformed_first_nonzero_of_z2_neg_one hz₁ hspecial

theorem standard_affine_fourier_six_corner_certificate
    {z₁ z₂ : ℂ} (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1) :
    ∃ r : I3, ∃ c : I2,
      leadingFiniteCornerWitnessProduct
        (seamCornerChart r c
          (affineFourierMatrix standardOmega z₁ z₂)) ≠ 0 := by
  by_cases hz₁m : z₁ = -1
  · subst z₁
    exact standard_z1_neg_one_six_corner_certificate hz₂
  · by_cases hz₂m : z₂ = -1
    · subst z₂
      exact standard_z2_neg_one_six_corner_certificate hz₁
    · exact standard_nonboundary_six_corner_certificate hz₁ hz₂ hz₁m hz₂m

/-- The paper's six-corner no-common-failure statement for its fixed standard
primitive cubic phase.  This is the public audit endpoint for the exact
common-zero elimination. -/
theorem standard_affine_fourier_six_corner_certificate_proved
    {z₁ z₂ : ℂ} (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1) :
    ∃ r : I3, ∃ c : I2,
      leadingFiniteCornerWitnessProduct
        (seamCornerChart r c
          (affineFourierMatrix standardOmega z₁ z₂)) ≠ 0 :=
  standard_affine_fourier_six_corner_certificate hz₁ hz₂

end

end Hadamard6
