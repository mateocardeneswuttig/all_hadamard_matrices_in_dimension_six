import Hadamard6.FourierSeamCertificatePullbacksA

namespace Hadamard6

noncomputable section

/-- The second factor of the swapped-row endpoint polynomial.  Separating it
from the common first factor keeps the exact norm certificate small. -/
def seamP_Bswap0Companion (z₁ z₂ : ℂ) : ℂ :=
  (-z₁ ^ 2 + (2 * standardOmega + 1) * z₁ ^ 2 +
    4 * z₁ * z₂ - 2 * z₁ -
    2 * (2 * standardOmega + 1) * z₁ - z₂ ^ 2 -
    (2 * standardOmega + 1) * z₂ ^ 2 - 2 * z₂ +
    2 * (2 * standardOmega + 1) * z₂ + 2) / 2

theorem seamP_Bswap0_factor (z₁ z₂ : ℂ) :
    seamP_Bswap0 z₁ z₂ =
      -(z₁ * z₂ + z₁ + z₂) * seamP_Bswap0Companion z₁ z₂ := by
  simp [seamP_Bswap0, seamP_Bswap0Companion]
  ring

set_option maxRecDepth 100000 in
theorem seamP_Bswap0Companion_pullback_norm (x y : ℝ) :
    Complex.normSq
        (seamDen x ^ 2 * seamDen y ^ 2 *
          seamP_Bswap0Companion (seamCayley x) (seamCayley y)) =
      16 * seamQminus x y ^ 2 := by
  rw [seamCayley_eq_coordinates, seamCayley_eq_coordinates]
  have hx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  simp [seamDen, seamP_Bswap0Companion, seamCayleyCoord, seamQminus,
    standardOmega, Complex.normSq_apply, pow_succ,
    Complex.mul_re, Complex.mul_im]
  field_simp [hx, hy]
  ring_nf
  simp only [s3_sq]
  ring

end

end Hadamard6
