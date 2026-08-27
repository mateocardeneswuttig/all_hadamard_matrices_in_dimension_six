import Hadamard6.KarlssonFourierSeam
import Hadamard6.TaoAtlas
import Mathlib.Tactic

/-!
# Kernel certificate for the affine-Fourier seam

This file is the Lean audit trail for the finite six-corner calculation in
the paper.  It deliberately treats only the exceptional affine-Fourier seam;
the regular Karlsson chart is proved separately in `KarlssonMixedBlocks`.
-/

namespace Hadamard6

noncomputable section

abbrev s3 : ℝ := Real.sqrt 3

/-- The real Cayley chart on the unit circle, missing only `-1`. -/
noncomputable def seamCayley (x : ℝ) : ℂ :=
  ((1 : ℂ) + Complex.I * (x : ℂ)) /
    ((1 : ℂ) - Complex.I * (x : ℂ))

theorem s3_sq : s3 ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num)

theorem s3_pos : 0 < s3 :=
  Real.sqrt_pos.2 (by norm_num)

theorem s3_pow3 : s3 ^ 3 = 3 * s3 := by
  calc s3 ^ 3 = s3 ^ 2 * s3 := by ring
       _ = 3 * s3 := by rw [s3_sq]

theorem s3_pow4 : s3 ^ 4 = 9 := by
  calc s3 ^ 4 = (s3 ^ 2) ^ 2 := by ring
       _ = 9 := by rw [s3_sq]; norm_num

theorem s3_pow5 : s3 ^ 5 = 9 * s3 := by
  calc s3 ^ 5 = (s3 ^ 2) ^ 2 * s3 := by ring
       _ = 9 * s3 := by rw [s3_sq]; norm_num

theorem s3_pow6 : s3 ^ 6 = 27 := by
  calc s3 ^ 6 = (s3 ^ 2) ^ 3 := by ring
       _ = 27 := by rw [s3_sq]; norm_num

theorem s3_pow7 : s3 ^ 7 = 27 * s3 := by
  calc s3 ^ 7 = (s3 ^ 2) ^ 3 * s3 := by ring
       _ = 27 * s3 := by rw [s3_sq]; norm_num

theorem s3_pow8 : s3 ^ 8 = 81 := by
  calc s3 ^ 8 = (s3 ^ 2) ^ 4 := by ring
       _ = 81 := by rw [s3_sq]; norm_num

theorem s3_pow9 : s3 ^ 9 = 81 * s3 := by
  calc s3 ^ 9 = (s3 ^ 2) ^ 4 * s3 := by ring
       _ = 81 * s3 := by rw [s3_sq]; norm_num

theorem s3_pow10 : s3 ^ 10 = 243 := by
  calc s3 ^ 10 = (s3 ^ 2) ^ 5 := by ring
       _ = 243 := by rw [s3_sq]; norm_num

theorem seamCayley_normSq (x : ℝ) :
    Complex.normSq (seamCayley x) = 1 := by
  have hn : Complex.normSq
      ((1 : ℂ) + Complex.I * (x : ℂ)) = 1 + x ^ 2 := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hd : Complex.normSq
      ((1 : ℂ) - Complex.I * (x : ℂ)) = 1 + x ^ 2 := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [seamCayley, Complex.normSq_div, hn, hd]
  exact div_self (by nlinarith [sq_nonneg x])

/-- Every unit phase other than `-1` has a real Cayley coordinate. -/
theorem exists_seamCayley_of_normSq_one {z : ℂ}
    (hz : Complex.normSq z = 1) (hne : z ≠ -1) :
    ∃ x : ℝ, z = seamCayley x := by
  have hcoords : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hz
  have hden : 1 + z.re ≠ 0 := by
    intro hzero
    have hre : z.re = -1 := by linarith
    have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
    apply hne
    apply Complex.ext <;> norm_num [hre, him]
  let x : ℝ := z.im / (1 + z.re)
  refine ⟨x, ?_⟩
  have hdenComplex : (1 : ℂ) - Complex.I * (x : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [Complex.mul_re] at hre
  rw [seamCayley, eq_div_iff hdenComplex]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    dsimp [x]
    field_simp [hden]
    nlinarith
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    dsimp [x]
    field_simp [hden]
    ring

theorem seamMinusDen_ne (x : ℝ) :
    (1 : ℂ) - Complex.I * (x : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [Complex.mul_re] at hre

theorem seamPlusDen_ne (x : ℝ) :
    (1 : ℂ) + Complex.I * (x : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [Complex.mul_re] at hre

theorem star_seamCayley (x : ℝ) :
    star (seamCayley x) =
      ((1 : ℂ) - Complex.I * (x : ℂ)) /
        ((1 : ℂ) + Complex.I * (x : ℂ)) := by
  simp [seamCayley, star_add, star_sub, star_mul]
  ring

noncomputable def seamCayleyCoord (x : ℝ) : ℂ :=
  ⟨(1 - x ^ 2) / (1 + x ^ 2), (2 * x) / (1 + x ^ 2)⟩

theorem seamCayley_eq_coordinates (x : ℝ) :
    seamCayley x = seamCayleyCoord x := by
  have hden : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  rw [seamCayley]
  apply (div_eq_iff (seamMinusDen_ne x)).2
  apply Complex.ext <;>
    simp [seamCayleyCoord, Complex.mul_re, Complex.mul_im] <;>
    field_simp [hden] <;> ring

theorem seamCayley_zero : seamCayley 0 = 1 := by
  norm_num [seamCayley]

theorem seamCayley_s3 : seamCayley s3 = standardOmega := by
  rw [seamCayley_eq_coordinates]
  apply Complex.ext <;>
    simp [seamCayleyCoord, standardOmega] <;>
    field_simp <;> nlinarith [s3_sq]

theorem seamCayley_neg_s3 : seamCayley (-s3) = standardOmega ^ 2 := by
  rw [seamCayley_eq_coordinates]
  apply Complex.ext <;>
    simp [seamCayleyCoord, standardOmega, pow_two,
      Complex.mul_re, Complex.mul_im] <;>
    field_simp <;> nlinarith [s3_sq]

theorem seamCayley_neg_third_s3 :
    seamCayley (-s3 / 3) = -standardOmega := by
  rw [seamCayley_eq_coordinates]
  apply Complex.ext <;>
    simp [seamCayleyCoord, standardOmega] <;>
    field_simp <;> nlinarith [s3_sq]

theorem seamCayley_third_s3 :
    seamCayley (s3 / 3) = -(standardOmega ^ 2) := by
  rw [seamCayley_eq_coordinates]
  apply Complex.ext <;>
    simp [seamCayleyCoord, standardOmega, pow_two,
      Complex.mul_re, Complex.mul_im] <;>
    field_simp <;> nlinarith [s3_sq]

/-- The first displayed positional corner, after its canonical dephasing. -/
def firstSeamChart (omega z₁ z₂ : ℂ) : Mat6 :=
  Matrix.fromBlocks
    !![1, 1, 1;
       1, z₁, z₂;
       1, omega, omega ^ 2]
    !![1, 1, 1;
       -1, -z₁, -z₂;
       1, omega, omega ^ 2]
    !![1, omega * z₁, omega ^ 2 * z₂;
       1, omega ^ 2, omega;
       1, omega ^ 2 * z₁, omega * z₂]
    !![-1, -(omega * z₁), -(omega ^ 2 * z₂);
       1, omega ^ 2, omega;
       -1, -(omega ^ 2 * z₁), -(omega * z₂)]

theorem seamCornerChart_zero_zero_eq
    {omega z₁ z₂ : ℂ} (_homega : IsPrimitiveCubicPhase omega)
    (_hz₁ : Complex.normSq z₁ = 1)
    (_hz₂ : Complex.normSq z₂ = 1) :
    seamCornerChart 0 0 (affineFourierMatrix omega z₁ z₂) =
      firstSeamChart omega z₁ z₂ := by
  have hreindex :
      reindexMatrix (seamRowPermutation 0) (seamColumnPermutation 0)
          (affineFourierMatrix omega z₁ z₂) =
        firstSeamChart omega z₁ z₂ := by
    rcases seamColumns024_order with
      ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [reindexMatrix, seamRowPermutation, seamColumnPermutation,
        seamRows012, hc0, hc1, hc2, hc3, hc4, hc5,
        affineFourierMatrix, firstSeamChart]
  rw [seamCornerChart, hreindex]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [dephase, phaseTransform, dephaseRowFactor, dephaseColumnFactor,
      firstSeamChart]

def seamA (x y : ℝ) : ℝ :=
  x ^ 2 * y ^ 2 + x ^ 2 + 8 * x * y + y ^ 2 + 9

def seamQminus (x y : ℝ) : ℝ :=
  x ^ 2 * y ^ 2 - s3 * x ^ 2 * y + x ^ 2 +
    s3 * x * y ^ 2 - x * y + y ^ 2

def seamQplus (x y : ℝ) : ℝ :=
  x ^ 2 * y ^ 2 + s3 * x ^ 2 * y + x ^ 2 -
    s3 * x * y ^ 2 - x * y + y ^ 2

def seamLminus (x y : ℝ) : ℝ :=
  x * y - s3 * x / 3 + s3 * y / 3 + 1

def seamLplus (x y : ℝ) : ℝ :=
  x * y + s3 * x / 3 - s3 * y / 3 + 1

theorem seamA_eq_sumsq (x y : ℝ) :
    seamA x y = (x * y + 3) ^ 2 + (x + y) ^ 2 := by
  simp [seamA]
  ring

theorem seamQminus_sumsq (x y : ℝ) :
    4 * (y ^ 2 - s3 * y + 1) * seamQminus x y =
      (2 * (y ^ 2 - s3 * y + 1) * x + (s3 * y ^ 2 - y)) ^ 2 +
        (y * (y - s3)) ^ 2 := by
  simp [seamQminus]
  ring_nf
  rw [s3_sq]
  ring

theorem seamQminus_zero_cases {x y : ℝ}
    (h : seamQminus x y = 0) :
    (x = 0 ∧ y = 0) ∨ (x = -s3 ∧ y = s3) := by
  have hid := seamQminus_sumsq x y
  rw [h] at hid
  have hlinear :
      2 * (y ^ 2 - s3 * y + 1) * x + (s3 * y ^ 2 - y) = 0 := by
    nlinarith [sq_nonneg
      (2 * (y ^ 2 - s3 * y + 1) * x + (s3 * y ^ 2 - y)),
      sq_nonneg (y * (y - s3))]
  have hyprod : y * (y - s3) = 0 := by
    nlinarith [sq_nonneg
      (2 * (y ^ 2 - s3 * y + 1) * x + (s3 * y ^ 2 - y)),
      sq_nonneg (y * (y - s3))]
  rcases mul_eq_zero.mp hyprod with hy | hy
  · left
    constructor
    · simp [hy] at hlinear
      linarith
    · exact hy
  · right
    have hy' : y = s3 := by linarith
    constructor
    · rw [hy'] at hlinear
      have hcub : s3 ^ 3 = 3 * s3 := by
        calc
          s3 ^ 3 = s3 * s3 ^ 2 := by ring
          _ = 3 * s3 := by rw [s3_sq]; ring
      nlinarith [s3_sq, hcub]
    · exact hy'

theorem seamQplus_zero_cases {x y : ℝ}
    (h : seamQplus x y = 0) :
    (x = 0 ∧ y = 0) ∨ (x = s3 ∧ y = -s3) := by
  have hminus : seamQminus (-x) (-y) = 0 := by
    have heq : seamQminus (-x) (-y) = seamQplus x y := by
      simp [seamQplus, seamQminus]
      ring
    rw [heq, h]
  rcases seamQminus_zero_cases hminus with hzero | hs
  · left
    constructor <;> linarith [hzero.1, hzero.2]
  · right
    constructor <;> linarith [hs.1, hs.2]

theorem seamA_zero_cases {x y : ℝ} (h : seamA x y = 0) :
    (x = s3 ∧ y = -s3) ∨ (x = -s3 ∧ y = s3) := by
  rw [seamA_eq_sumsq] at h
  have hxy : x * y + 3 = 0 := by
    nlinarith [sq_nonneg (x * y + 3), sq_nonneg (x + y)]
  have hsum : x + y = 0 := by
    nlinarith [sq_nonneg (x * y + 3), sq_nonneg (x + y)]
  have hsquare : x ^ 2 = 3 := by nlinarith
  have hfactor : (x - s3) * (x + s3) = 0 := by
    nlinarith [s3_sq]
  rcases mul_eq_zero.mp hfactor with hx | hx
  · left
    constructor <;> linarith
  · right
    constructor <;> linarith

/-- Cleared exact determinant formula for the first seam corner. -/
theorem firstSeam_detE_cayley_clear (x y : ℝ) :
    (((x : ℂ) + Complex.I) * ((y : ℂ) + Complex.I)) *
        (Matrix.toBlocks₁₁
          (firstSeamChart standardOmega (seamCayley x)
            (seamCayley y))).det =
      (-(s3 : ℂ) * ((x : ℂ) + (y : ℂ))) +
        Complex.I * (2 * (s3 : ℂ) *
          ((x : ℂ) * (y : ℂ) +
            (s3 : ℂ) * ((x : ℂ) - (y : ℂ)) / 2)) := by
  rw [seamCayley_eq_coordinates, seamCayley_eq_coordinates]
  have hx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  apply Complex.ext <;>
    simp [firstSeamChart, standardOmega, Matrix.det_fin_three,
      seamCayleyCoord, pow_two, Complex.mul_re, Complex.mul_im] <;>
    field_simp [hx, hy] <;>
    ring_nf <;>
    simp only [s3_sq] <;> ring

theorem firstSeam_detB_cayley_clear (x y : ℝ) :
    (((x : ℂ) + Complex.I) * ((y : ℂ) + Complex.I)) *
        (Matrix.toBlocks₁₂
          (firstSeamChart standardOmega (seamCayley x)
            (seamCayley y))).det =
      ((s3 : ℂ) * ((x : ℂ) + (y : ℂ))) -
        Complex.I * (2 * (s3 : ℂ) *
          ((x : ℂ) * (y : ℂ) +
            (s3 : ℂ) * ((x : ℂ) - (y : ℂ)) / 2)) := by
  rw [seamCayley_eq_coordinates, seamCayley_eq_coordinates]
  have hx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  apply Complex.ext <;>
    simp [firstSeamChart, standardOmega, Matrix.det_fin_three,
      seamCayleyCoord, pow_two, Complex.mul_re, Complex.mul_im] <;>
    field_simp [hx, hy] <;>
    ring_nf <;>
    simp only [s3_sq] <;> ring

theorem firstSeam_detC_cayley_clear (x y : ℝ) :
    (((x : ℂ) + Complex.I) * ((y : ℂ) + Complex.I)) *
        (Matrix.toBlocks₂₁
          (firstSeamChart standardOmega (seamCayley x)
            (seamCayley y))).det =
      ((s3 : ℂ) * ((x : ℂ) + (y : ℂ))) +
        Complex.I * (2 * (s3 : ℂ) *
          ((x : ℂ) * (y : ℂ) +
            (s3 : ℂ) * ((x : ℂ) - (y : ℂ)) / 2)) := by
  rw [seamCayley_eq_coordinates, seamCayley_eq_coordinates]
  have hx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  apply Complex.ext <;>
    simp [firstSeamChart, standardOmega, Matrix.det_fin_three,
      seamCayleyCoord, pow_two, Complex.mul_re, Complex.mul_im] <;>
    field_simp [hx, hy] <;>
    ring_nf <;>
    simp only [s3_sq, s3_pow3, s3_pow4] <;> ring


end

end Hadamard6
