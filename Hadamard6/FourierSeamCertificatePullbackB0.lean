import Hadamard6.FourierSeamCertificateFormulasC

namespace Hadamard6

noncomputable section

def seamDen (x : ℝ) : ℂ :=
  1 - Complex.I * (x : ℂ)

set_option maxRecDepth 100000 in
theorem seamP_B0_pullback_norm (x y : ℝ) :
    Complex.normSq
        (seamDen x ^ 2 * seamDen y ^ 2 *
          seamP_B0 (seamCayley x) (seamCayley y)) =
      4 * seamA x y * seamQminus x y := by
  rw [seamCayley_eq_coordinates, seamCayley_eq_coordinates]
  have hx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  simp [seamDen, seamP_B0, seamCayleyCoord, seamA, seamQminus,
    standardOmega, Complex.normSq_apply, pow_succ,
    Complex.mul_re, Complex.mul_im]
  field_simp [hx, hy]
  ring_nf
  simp only [s3_sq, s3_pow3, s3_pow4]
  ring

set_option maxRecDepth 100000 in

end

end Hadamard6
