import Hadamard6.FourierSeamCertificateAlgebra

namespace Hadamard6

noncomputable section

def seamP_B0 (z₁ z₂ : ℂ) : ℂ :=
  (z₁ * z₂ + z₁ + z₂) *
    (z₁ * z₂ + standardOmega ^ 2 * z₁ + standardOmega * z₂)

def seamP_B3 (z₁ z₂ : ℂ) : ℂ :=
  (z₁ * z₂ + z₁ + z₂) ^ 2 *
    (standardOmega ^ 2 * z₁ + standardOmega * z₂ + 1)

def seamP_Bswap0 (z₁ z₂ : ℂ) : ℂ :=
  -(z₁ * z₂ + z₁ + z₂) *
    (-z₁ ^ 2 + (2 * standardOmega + 1) * z₁ ^ 2 +
      4 * z₁ * z₂ - 2 * z₁ -
      2 * (2 * standardOmega + 1) * z₁ - z₂ ^ 2 -
      (2 * standardOmega + 1) * z₂ ^ 2 - 2 * z₂ +
      2 * (2 * standardOmega + 1) * z₂ + 2) / 2

def seamK : ℂ := 2 * standardOmega + 1

def seamP_C0 (z₁ z₂ : ℂ) : ℂ :=
  3 * z₁ ^ 2 * z₂ - z₁ * z₂ ^ 3 + z₁ * z₂ ^ 2 -
    seamK * z₁ * z₂ ^ 2 + z₁ * z₂ + seamK * z₁ * z₂ -
    z₁ - z₂ ^ 3 - seamK * z₂ ^ 3 - z₂ ^ 2 - z₂ + seamK * z₂

def seamP_C3 (z₁ z₂ : ℂ) : ℂ :=
  z₁ ^ 3 - 3 * z₁ ^ 2 * z₂ ^ 2 - z₁ ^ 2 * z₂ +
    seamK * z₁ ^ 2 * z₂ + z₁ ^ 2 + seamK * z₁ ^ 2 -
    z₁ * z₂ ^ 2 - seamK * z₁ * z₂ ^ 2 + z₁ * z₂ +
    z₂ ^ 3 + z₂ ^ 2 - seamK * z₂ ^ 2

def seamP_Cswap0 (z₁ z₂ : ℂ) : ℂ :=
  -(z₁ ^ 3 * z₂ + z₁ ^ 3 - seamK * z₁ ^ 3 -
    z₁ ^ 2 * z₂ - seamK * z₁ ^ 2 * z₂ + z₁ ^ 2 -
    3 * z₁ * z₂ ^ 2 - z₁ * z₂ + seamK * z₁ * z₂ +
    z₁ + seamK * z₁ + z₂)

theorem firstSeam_B0_formula {z₁ z₂ : ℂ}
    (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1) :
    z₁ ^ 2 * z₂ ^ 2 *
        rowEndpoint0 (Matrix.toBlocks₁₂
          (firstSeamChart standardOmega z₁ z₂)) =
      3 * seamP_B0 z₁ z₂ := by
  have hs1 : star z₁ = 1 / z₁ := by
    exact (one_div_eq_star_of_normSq_eq_one hz₁).symm
  have hs2 : star z₂ = 1 / z₂ := by
    exact (one_div_eq_star_of_normSq_eq_one hz₂).symm
  rw [rowEndpoint0_eq_fibreData _ (by intro j; fin_cases j <;> rfl)]
  simp [firstSeamChart, seamP_B0, fibreS, fibreT, fibreR,
    hs1, hs2, standardOmega]
  field_simp [ne_zero_of_normSq_eq_one hz₁,
    ne_zero_of_normSq_eq_one hz₂]
  apply Complex.ext <;>
    simp [pow_succ, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;>
    simp only [s3_sq, s3_pow3, s3_pow4, s3_pow5, s3_pow6] <;> ring

set_option maxRecDepth 100000 in
theorem firstSeam_B3_formula {z₁ z₂ : ℂ}
    (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1) :
    z₁ ^ 2 * z₂ ^ 2 *
        rowEndpoint3 (Matrix.toBlocks₁₂
          (firstSeamChart standardOmega z₁ z₂)) =
      seamP_B3 z₁ z₂ := by
  have hs1 : star z₁ = 1 / z₁ := by
    exact (one_div_eq_star_of_normSq_eq_one hz₁).symm
  have hs2 : star z₂ = 1 / z₂ := by
    exact (one_div_eq_star_of_normSq_eq_one hz₂).symm
  rw [rowEndpoint3_eq_fibreData _ (by intro j; fin_cases j <;> rfl)]
  simp [firstSeamChart, seamP_B3, fibreS, fibreT, fibreR,
    hs1, hs2, standardOmega]
  field_simp [ne_zero_of_normSq_eq_one hz₁,
    ne_zero_of_normSq_eq_one hz₂]
  apply Complex.ext <;>
    simp [pow_succ, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;>
    simp only [s3_sq, s3_pow3, s3_pow4, s3_pow5, s3_pow6] <;> ring

set_option maxRecDepth 100000 in
theorem firstSeam_Bswap0_formula {z₁ z₂ : ℂ}
    (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1) :
    z₁ * z₂ *
        rowEndpoint0 (swapNoninitialRows (Matrix.toBlocks₁₂
          (firstSeamChart standardOmega z₁ z₂))) =
      seamP_Bswap0 z₁ z₂ := by
  have hs1 : star z₁ = 1 / z₁ :=
    (one_div_eq_star_of_normSq_eq_one hz₁).symm
  have hs2 : star z₂ = 1 / z₂ :=
    (one_div_eq_star_of_normSq_eq_one hz₂).symm
  rw [rowEndpoint0_eq_fibreData _ (by intro j; fin_cases j <;> rfl)]
  simp [firstSeamChart, swapNoninitialRows, seamP_Bswap0,
    fibreS, fibreT, fibreR, hs1, hs2, standardOmega]
  field_simp [ne_zero_of_normSq_eq_one hz₁,
    ne_zero_of_normSq_eq_one hz₂]
  apply Complex.ext <;>
    simp [pow_succ, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;>
    simp only [s3_sq, s3_pow3, s3_pow4] <;> ring


end

end Hadamard6
