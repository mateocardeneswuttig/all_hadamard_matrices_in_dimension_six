import Hadamard6.FourierSeamCertificateFormulasC0

namespace Hadamard6

noncomputable section

set_option maxRecDepth 100000 in
theorem firstSeam_Cswap0_formula {z₁ z₂ : ℂ}
    (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1) :
    z₁ * z₂ ^ 2 *
        rowEndpoint0 (swapNoninitialRows ((Matrix.toBlocks₂₁
          (firstSeamChart standardOmega z₁ z₂)).transpose)) =
      seamP_Cswap0 z₁ z₂ := by
  have hs1 : star z₁ = 1 / z₁ :=
    (one_div_eq_star_of_normSq_eq_one hz₁).symm
  have hs2 : star z₂ = 1 / z₂ :=
    (one_div_eq_star_of_normSq_eq_one hz₂).symm
  rw [rowEndpoint0_eq_fibreData _ (by intro j; fin_cases j <;> rfl)]
  simp [firstSeamChart, swapNoninitialRows, seamP_Cswap0, seamK,
    fibreS, fibreT, fibreR, hs1, hs2, standardOmega]
  field_simp [ne_zero_of_normSq_eq_one hz₁,
    ne_zero_of_normSq_eq_one hz₂]
  apply Complex.ext <;>
    simp [pow_two, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;>
    simp only [s3_sq, s3_pow3, s3_pow4, s3_pow5, s3_pow6,
      s3_pow7, s3_pow8, s3_pow9] <;> ring

set_option maxRecDepth 100000 in
theorem firstSeam_Bswap3_formula {z₁ z₂ : ℂ}
    (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1) :
    z₁ ^ 2 * z₂ ^ 2 *
        rowEndpoint3 (swapNoninitialRows (Matrix.toBlocks₁₂
          (firstSeamChart standardOmega z₁ z₂))) =
      seamP_B3 z₁ z₂ := by
  have hs1 : star z₁ = 1 / z₁ :=
    (one_div_eq_star_of_normSq_eq_one hz₁).symm
  have hs2 : star z₂ = 1 / z₂ :=
    (one_div_eq_star_of_normSq_eq_one hz₂).symm
  rw [rowEndpoint3_eq_fibreData _ (by intro j; fin_cases j <;> rfl)]
  simp [firstSeamChart, swapNoninitialRows, seamP_B3,
    fibreS, fibreT, fibreR, hs1, hs2, standardOmega]
  field_simp [ne_zero_of_normSq_eq_one hz₁,
    ne_zero_of_normSq_eq_one hz₂]
  apply Complex.ext <;>
    simp [pow_succ, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;>
    simp only [s3_sq, s3_pow3, s3_pow4, s3_pow5, s3_pow6] <;> ring


end

end Hadamard6
