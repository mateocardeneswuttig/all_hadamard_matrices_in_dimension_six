import Hadamard6.FourierSeamCertificatePullbackBswap0

namespace Hadamard6

noncomputable section

set_option maxRecDepth 100000 in
theorem seamP_C0_pullback (x y : ℝ) :
    seamDen x ^ 2 * seamDen y ^ 3 *
        seamP_C0 (seamCayley x) (seamCayley y) =
      ⟨2 * s3 * y * (x + s3) * (y + s3) * seamLminus x y,
        2 * (y - s3) ^ 2 * (x ^ 2 * y + 2 * x - y)⟩ := by
  rw [seamCayley_eq_coordinates, seamCayley_eq_coordinates]
  have hx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  apply Complex.ext <;>
    simp [seamDen, seamP_C0, seamK, seamLminus, seamCayleyCoord,
      standardOmega, pow_succ, Complex.mul_re, Complex.mul_im] <;>
    field_simp [hx, hy] <;>
    ring_nf <;>
    simp only [s3_sq, s3_pow3, s3_pow4] <;> ring

end

end Hadamard6
