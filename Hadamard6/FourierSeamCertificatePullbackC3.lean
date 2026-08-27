import Hadamard6.FourierSeamCertificatePullbacksB

namespace Hadamard6

noncomputable section

set_option maxRecDepth 100000 in
theorem seamP_C3_pullback (x y : ℝ) :
    seamDen x ^ 3 * seamDen y ^ 3 *
        seamP_C3 (seamCayley x) (seamCayley y) =
      ⟨2 * s3 * (x + s3) * (x - y) * (y - s3) * seamLplus x y,
        -(6 * (x + y) * seamLminus x y ^ 2)⟩ := by
  rw [seamCayley_eq_coordinates, seamCayley_eq_coordinates]
  have hx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  apply Complex.ext <;>
    simp [seamDen, seamP_C3, seamK, seamLminus, seamLplus,
      seamCayleyCoord, standardOmega, pow_succ,
      Complex.mul_re, Complex.mul_im] <;>
    field_simp [hx, hy] <;>
    ring_nf <;>
    simp only [s3_sq, s3_pow3, s3_pow4] <;> ring

end

end Hadamard6
