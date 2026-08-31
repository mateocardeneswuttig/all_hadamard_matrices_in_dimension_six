import Hadamard6.FourierSeamCertificatePullbackC3

namespace Hadamard6

noncomputable section

theorem seamP_Cswap0_pullback (x y : ℝ) :
    seamDen x ^ 3 * seamDen y ^ 2 *
        seamP_Cswap0 (seamCayley x) (seamCayley y) =
      ⟨-(2 * s3 * x * (x - s3) * (y - s3) * seamLminus x y),
        2 * (x + s3) ^ 2 * (x * y ^ 2 - x + 2 * y)⟩ := by
  rw [seamCayley_eq_coordinates, seamCayley_eq_coordinates]
  have hx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  apply Complex.ext <;>
    simp [seamDen, seamP_Cswap0, seamK, seamLminus,
      seamCayleyCoord, standardOmega, pow_succ,
      Complex.mul_re, Complex.mul_im] <;>
    field_simp [hx, hy] <;>
    ring_nf <;>
    simp only [s3_sq, s3_pow3, s3_pow4] <;> ring

/-- The six finite Cayley pairs at which the first seam corner can fail. -/
def FirstSeamExceptional (x y : ℝ) : Prop :=
  (x = 0 ∧ y = 0) ∨
  (x = s3 ∧ y = -s3) ∨
  (x = -s3 ∧ y = s3) ∨
  (x = -s3 / 3 ∧ y = -s3) ∨
  (x = -s3 / 3 ∧ y = s3 / 3) ∨
  (x = s3 ∧ y = s3 / 3)


end

end Hadamard6
