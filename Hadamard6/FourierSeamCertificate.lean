import Hadamard6.FourierSeamCertificateBoundary

namespace Hadamard6

noncomputable section

/-! Transposition swaps the two intrinsic fibre problems.  These lemmas let
the paper treat the transposed affine-Fourier seam structurally instead of
repeating the six-corner polynomial calculation. -/

theorem transposeGram_involutive (G : Mat3) :
    transposeGram (transposeGram G) = G := by
  rfl

theorem transpose_columnGram (X : Mat3) :
    Matrix.conjTranspose X.transpose * X.transpose =
      transposeGram (X * Matrix.conjTranspose X) := by
  ext i j
  simp only [transposeGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem transpose_mem_normalizedColumnGramFibre
    {G X : Mat3} (hX : X ∈ normalizedRowGramFibre (transposeGram G)) :
    X.transpose ∈ normalizedColumnGramFibre G := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact hX.1 j i
  · intro i
    exact hX.2.1 i
  · rw [transpose_columnGram, hX.2.2, transposeGram_involutive]

theorem finite_row_transpose_of_finite_column {G : Mat3}
    (hfin : (normalizedColumnGramFibre G).Finite) :
    (normalizedRowGramFibre (transposeGram G)).Finite := by
  by_contra hinf
  have hinfinite :
      (normalizedRowGramFibre (transposeGram G)).Infinite := hinf
  have himage := hinfinite.image
    (fun _ _ _ _ h ↦ transpose_injective h)
  have hsubset : (Matrix.transpose ''
      normalizedRowGramFibre (transposeGram G)) ⊆
      normalizedColumnGramFibre G := by
    rintro Y ⟨X, hX, rfl⟩
    exact transpose_mem_normalizedColumnGramFibre hX
  exact himage (hfin.subset hsubset)

theorem finite_column_transpose_of_finite_row {G : Mat3}
    (hfin : (normalizedRowGramFibre G).Finite) :
    (normalizedColumnGramFibre (transposeGram G)).Finite := by
  by_contra hinf
  have hinf' := infinite_column_fibre_transpose hinf
  rw [transposeGram_involutive] at hinf'
  exact hinf' hfin

theorem toBlocks₁₁_transpose (H : Mat6) :
    Matrix.toBlocks₁₁ H.transpose = (Matrix.toBlocks₁₁ H).transpose := by
  rfl

theorem toBlocks₁₂_transpose (H : Mat6) :
    Matrix.toBlocks₁₂ H.transpose = (Matrix.toBlocks₂₁ H).transpose := by
  rfl

theorem toBlocks₂₁_transpose (H : Mat6) :
    Matrix.toBlocks₂₁ H.transpose = (Matrix.toBlocks₁₂ H).transpose := by
  rfl

theorem transpose_hasFiniteCorner_of_leading {H : Mat6}
    (hH : IsHadamard H) (h : LeadingFiniteCornerCertificate H) :
    HasFiniteCorner H.transpose := by
  apply finite_topLeft_intrinsic_fibres_give_finiteCorner
    (transpose_isHadamard hH)
  · rw [toBlocks₁₁_transpose]
    exact transpose_det_ne_zero h.detE
  · rw [toBlocks₁₂_transpose]
    exact transpose_det_ne_zero h.detC
  · rw [toBlocks₂₁_transpose]
    exact transpose_det_ne_zero h.detB
  · rw [toBlocks₁₂_transpose, transpose_rowGram]
    exact finite_row_transpose_of_finite_column
      (normalizedColumnGramFibre_finite_of_transpose_endpoints
        h.C_endpoint0 h.C_endpoint3
        h.C_swapped_endpoint0 h.C_swapped_endpoint3)
  · rw [toBlocks₂₁_transpose, transpose_columnGram]
    exact finite_column_transpose_of_finite_row
      (normalizedRowGramFibre_finite_of_matrix_endpoints
        h.B_endpoint0 h.B_endpoint3
        h.B_swapped_endpoint0 h.B_swapped_endpoint3)

theorem equivalent_transpose {H K : Mat6}
    (hHK : Equivalent H K) : Equivalent H.transpose K.transpose := by
  rcases hHK with ⟨σ, τ, r, c, hr, hc, hpres⟩
  refine ⟨τ, σ, c, r, hc, hr, ?_⟩
  intro i j
  simp only [Matrix.transpose_apply]
  rw [hpres]
  ring

theorem primitiveCubicPhase_eq_standard_or_sq
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega) :
    omega = standardOmega ∨ omega = standardOmega ^ 2 := by
  have hstandard := standardOmega_isPrimitiveCubicPhase
  have hsum : standardOmega + standardOmega ^ 2 = -1 := by
    linear_combination hstandard.2
  have hcube : standardOmega ^ 3 = 1 :=
    primitiveCubicPhase_cube hstandard
  have hfactor :
      (omega - standardOmega) * (omega - standardOmega ^ 2) = 0 := by
    calc
      (omega - standardOmega) * (omega - standardOmega ^ 2) =
          omega ^ 2 - (standardOmega + standardOmega ^ 2) * omega +
            standardOmega ^ 3 := by ring
      _ = omega ^ 2 + omega + 1 := by rw [hsum, hcube]; ring
      _ = 0 := homega.2
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

def omegaSquaredRowPermutation : Equiv.Perm I6 :=
  (Equiv.swap (Sum.inl 2) (Sum.inr 1)).trans
    (Equiv.swap (Sum.inr 0) (Sum.inr 2))

theorem omegaSquaredRowPermutation_order :
    omegaSquaredRowPermutation (Sum.inl 0) = Sum.inl 0 ∧
    omegaSquaredRowPermutation (Sum.inl 1) = Sum.inl 1 ∧
    omegaSquaredRowPermutation (Sum.inl 2) = Sum.inr 1 ∧
    omegaSquaredRowPermutation (Sum.inr 0) = Sum.inr 2 ∧
    omegaSquaredRowPermutation (Sum.inr 1) = Sum.inl 2 ∧
    omegaSquaredRowPermutation (Sum.inr 2) = Sum.inr 0 := by
  decide

theorem reindex_standardOmega_eq_squaredOmega (z₁ z₂ : ℂ) :
    reindexMatrix omegaSquaredRowPermutation (Equiv.refl I6)
        (affineFourierMatrix standardOmega z₁ z₂) =
      affineFourierMatrix (standardOmega ^ 2) z₁ z₂ := by
  rcases omegaSquaredRowPermutation_order with
    ⟨h0, h1, h2, h3, h4, h5⟩
  have homega := standardOmega_isPrimitiveCubicPhase
  have hcube : standardOmega ^ 3 = 1 :=
    primitiveCubicPhase_cube homega
  have hpow4 : standardOmega ^ 4 = standardOmega := by
    calc
      standardOmega ^ 4 = standardOmega * standardOmega ^ 3 := by ring
      _ = standardOmega := by rw [hcube, mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [reindexMatrix, h0, h1, h2, h3, h4, h5,
      affineFourierMatrix] <;>
    ring_nf <;> simp [hpow4]

theorem standard_affine_fourier_mem_finiteCornerAtlas
    {z₁ z₂ : ℂ} (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1) :
    InFiniteCornerAtlas (affineFourierMatrix standardOmega z₁ z₂) := by
  rcases standard_affine_fourier_six_corner_certificate hz₁ hz₂ with
    ⟨r, c, hproduct⟩
  have hfourier := affineFourierMatrix_isHadamard
    standardOmega_isPrimitiveCubicPhase hz₁ hz₂
  have hleading : LeadingFiniteCornerCertificate
      (seamCornerChart r c
        (affineFourierMatrix standardOmega z₁ z₂)) :=
    leadingFiniteCornerCertificate_iff_witnessProduct_ne_zero.2 hproduct
  have heq : Equivalent (affineFourierMatrix standardOmega z₁ z₂)
      (seamCornerChart r c
        (affineFourierMatrix standardOmega z₁ z₂)) :=
    equivalent_seamCornerChart hfourier.1 r c
  have hcorner := (equivalent_isHadamard_iff heq).1 hfourier
  exact inFiniteCornerAtlas_of_equivalent heq
    (finiteCorner_mem_finiteCornerAtlas
      (leadingFiniteCornerCertificate_hasFiniteCorner hcorner hleading))

theorem standard_transposed_affine_fourier_mem_finiteCornerAtlas
    {z₁ z₂ : ℂ} (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1) :
    InFiniteCornerAtlas
      (affineFourierMatrix standardOmega z₁ z₂).transpose := by
  rcases standard_affine_fourier_six_corner_certificate hz₁ hz₂ with
    ⟨r, c, hproduct⟩
  have hfourier := affineFourierMatrix_isHadamard
    standardOmega_isPrimitiveCubicPhase hz₁ hz₂
  have hleading : LeadingFiniteCornerCertificate
      (seamCornerChart r c
        (affineFourierMatrix standardOmega z₁ z₂)) :=
    leadingFiniteCornerCertificate_iff_witnessProduct_ne_zero.2 hproduct
  have heq : Equivalent (affineFourierMatrix standardOmega z₁ z₂)
      (seamCornerChart r c
        (affineFourierMatrix standardOmega z₁ z₂)) :=
    equivalent_seamCornerChart hfourier.1 r c
  have hcorner := (equivalent_isHadamard_iff heq).1 hfourier
  exact inFiniteCornerAtlas_of_equivalent (equivalent_transpose heq)
    (finiteCorner_mem_finiteCornerAtlas
      (transpose_hasFiniteCorner_of_leading hcorner hleading))

theorem affineFourierMatrix_mem_finiteCornerAtlas
    {omega z₁ z₂ : ℂ} (homega : IsPrimitiveCubicPhase omega)
    (hz₁ : Complex.normSq z₁ = 1) (hz₂ : Complex.normSq z₂ = 1) :
    InFiniteCornerAtlas (affineFourierMatrix omega z₁ z₂) := by
  rcases primitiveCubicPhase_eq_standard_or_sq homega with h | h
  · subst omega
    exact standard_affine_fourier_mem_finiteCornerAtlas hz₁ hz₂
  · subst omega
    have heq0 := equivalent_reindexMatrix omegaSquaredRowPermutation
      (Equiv.refl I6) (affineFourierMatrix standardOmega z₁ z₂)
    have heq : Equivalent (affineFourierMatrix standardOmega z₁ z₂)
        (affineFourierMatrix (standardOmega ^ 2) z₁ z₂) := by
      simpa [reindex_standardOmega_eq_squaredOmega] using heq0
    exact inFiniteCornerAtlas_of_equivalent (equivalent_symm heq)
      (standard_affine_fourier_mem_finiteCornerAtlas hz₁ hz₂)

theorem transposedAffineFourierMatrix_mem_finiteCornerAtlas
    {omega z₁ z₂ : ℂ} (homega : IsPrimitiveCubicPhase omega)
    (hz₁ : Complex.normSq z₁ = 1) (hz₂ : Complex.normSq z₂ = 1) :
    InFiniteCornerAtlas (affineFourierMatrix omega z₁ z₂).transpose := by
  rcases primitiveCubicPhase_eq_standard_or_sq homega with h | h
  · subst omega
    exact standard_transposed_affine_fourier_mem_finiteCornerAtlas hz₁ hz₂
  · subst omega
    have heq0 := equivalent_reindexMatrix omegaSquaredRowPermutation
      (Equiv.refl I6) (affineFourierMatrix standardOmega z₁ z₂)
    have heq : Equivalent (affineFourierMatrix standardOmega z₁ z₂)
        (affineFourierMatrix (standardOmega ^ 2) z₁ z₂) := by
      simpa [reindex_standardOmega_eq_squaredOmega] using heq0
    exact inFiniteCornerAtlas_of_equivalent
      (equivalent_symm (equivalent_transpose heq))
      (standard_transposed_affine_fourier_mem_finiteCornerAtlas hz₁ hz₂)

/-- Unconditional affine-Fourier seam inclusion, replacing the former
`FourierSeamFiniteCornerCertificate` argument in the classification chain. -/
theorem affineFourierSeam_mem_finiteCornerAtlas_proved
    {H : Mat6} (hH : IsAffineFourierSeam H) :
    InFiniteCornerAtlas H := by
  rcases hH with ⟨omega, z₁, z₂, homega, hz₁, hz₂, hpres⟩
  rcases hpres with hpres | hpres
  · exact inFiniteCornerAtlas_of_equivalent hpres
      (affineFourierMatrix_mem_finiteCornerAtlas homega hz₁ hz₂)
  · exact inFiniteCornerAtlas_of_equivalent hpres
      (transposedAffineFourierMatrix_mem_finiteCornerAtlas homega hz₁ hz₂)

end

end Hadamard6
