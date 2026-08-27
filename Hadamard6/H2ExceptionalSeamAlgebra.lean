import Hadamard6.H2KarlssonParametrization
import Hadamard6.KarlssonFourierSeam
import Hadamard6.TaoAtlas
import Mathlib.Tactic

/-!
# Algebra at the residual intrinsic `H₂` seam

This file contains the small scalar identities needed to identify the four
diagonal core remainders and the common half-angle point with the explicit
affine-Fourier seam.  No coverage or parametrization statement is assumed.
-/

namespace Hadamard6

noncomputable section

/-- Recover the first inverse-Fourier core directly from its intrinsic
Hermitian involution. -/
theorem h2ParameterA_eq_core_from_lambda
    {A L : Mat2} (hL : h2KarlssonLambda A = L) :
    A = karlssonF2 *
      ((-(1 / 2 : ℂ)) • (1 : Mat2) +
        (Complex.I * (Real.sqrt 3 : ℂ) / 2) • L) := by
  have hU := h2KarlssonUnitary_eq_lambda A
  rw [hL] at hU
  have hrecover : karlssonF2 * h2KarlssonUnitary A = A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h2KarlssonUnitary, karlssonF2,
        Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two] <;> ring
  rw [← hrecover, hU]

theorem core_from_lambda_one :
    karlssonF2 *
      ((-(1 / 2 : ℂ)) • (1 : Mat2) +
        (Complex.I * (Real.sqrt 3 : ℂ) / 2) • (1 : Mat2)) =
      standardOmega • karlssonF2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [karlssonF2, standardOmega, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]

theorem core_from_lambda_neg_one :
    karlssonF2 *
      ((-(1 / 2 : ℂ)) • (1 : Mat2) +
        (Complex.I * (Real.sqrt 3 : ℂ) / 2) • (-(1 : Mat2))) =
      standardOmega ^ 2 • karlssonF2 := by
  have hs3 : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [karlssonF2, standardOmega, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, pow_two] <;>
    nlinarith

theorem h2ParameterA_eq_omega_f2_of_lambda_one
    {A : Mat2} (hL : h2KarlssonLambda A = (1 : Mat2)) :
    A = standardOmega • karlssonF2 := by
  rw [h2ParameterA_eq_core_from_lambda hL, core_from_lambda_one]

theorem h2ParameterA_eq_omega_sq_f2_of_lambda_neg_one
    {A : Mat2} (hL : h2KarlssonLambda A = -(1 : Mat2)) :
    A = standardOmega ^ 2 • karlssonF2 := by
  rw [h2ParameterA_eq_core_from_lambda hL, core_from_lambda_neg_one]

/-- The complementary inverse-Fourier core is forced by `A+B=-F₂`. -/
theorem h2ParameterB_eq_omega_sq_f2_of_A_eq_omega_f2
    {A B : Mat2} (hsum : A + B = -karlssonF2)
    (hA : A = standardOmega • karlssonF2) :
    B = standardOmega ^ 2 • karlssonF2 := by
  have hsumOmega : 1 + standardOmega + standardOmega ^ 2 = 0 :=
    by linear_combination standardOmega_isPrimitiveCubicPhase.2
  have hscalar : -1 - standardOmega = standardOmega ^ 2 := by
    linear_combination -hsumOmega
  have hscalarNeg : 1 + standardOmega = -(standardOmega ^ 2) := by
    calc
      1 + standardOmega = -(-1 - standardOmega) := by ring
      _ = -(standardOmega ^ 2) := by rw [hscalar]
  have hB : B = -karlssonF2 - A := by
    ext i j
    have hij := congrArg (fun M : Mat2 ↦ M i j) hsum
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply] at hij ⊢
    linear_combination hij
  rw [hB, hA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [karlssonF2, hscalar, hscalarNeg]

theorem h2ParameterB_eq_omega_f2_of_A_eq_omega_sq_f2
    {A B : Mat2} (hsum : A + B = -karlssonF2)
    (hA : A = standardOmega ^ 2 • karlssonF2) :
    B = standardOmega • karlssonF2 := by
  have hsumOmega : 1 + standardOmega + standardOmega ^ 2 = 0 :=
    by linear_combination standardOmega_isPrimitiveCubicPhase.2
  have hscalar : -1 - standardOmega ^ 2 = standardOmega := by
    linear_combination -hsumOmega
  have hscalarNeg : 1 + standardOmega ^ 2 = -standardOmega := by
    calc
      1 + standardOmega ^ 2 = -(-1 - standardOmega ^ 2) := by ring
      _ = -standardOmega := by rw [hscalar]
  have hB : B = -karlssonF2 - A := by
    ext i j
    have hij := congrArg (fun M : Mat2 ↦ M i j) hsum
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply] at hij ⊢
    linear_combination hij
  rw [hB, hA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [karlssonF2, hscalar, hscalarNeg]

/-- A unit entry in a scalar-Fourier central block forces one of the two
adjacent phase squares to be one.  This is the exact midpoint-rigidity
factorization `(zL²-1)(zR²-1)=0`. -/
theorem scalarFourierBlock_unit_forces_square_one
    {omega zL zR : ℂ}
    (homega : Complex.normSq omega = 1)
    (hzL : Complex.normSq zL = 1)
    (hzR : Complex.normSq zR = 1)
    (hunit : Complex.normSq
      (karlssonBlockProduct zL (omega • karlssonF2) zR 0 0) = 1) :
    zL ^ 2 = 1 ∨ zR ^ 2 = 1 := by
  have hω0 := ne_zero_of_normSq_eq_one homega
  have hzL0 := ne_zero_of_normSq_eq_one hzL
  have hzR0 := ne_zero_of_normSq_eq_one hzR
  have hsω : (starRingEnd ℂ) omega = 1 / omega :=
    (one_div_eq_star_of_normSq_eq_one homega).symm
  have hsL : (starRingEnd ℂ) zL = 1 / zL :=
    (one_div_eq_star_of_normSq_eq_one hzL).symm
  have hsR : (starRingEnd ℂ) zR = 1 / zR :=
    (one_div_eq_star_of_normSq_eq_one hzR).symm
  have hunitC :
      ((Complex.normSq
        (karlssonBlockProduct zL (omega • karlssonF2) zR 0 0) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hunit
  simp [karlssonBlockProduct, karlssonZLeft, karlssonZRight,
    karlssonF2, Complex.normSq_eq_conj_mul_self,
    map_add, map_mul, hsω, hsL, hsR] at hunitC
  field_simp [hω0, hzL0, hzR0] at hunitC
  have hfactor : (zL ^ 2 - 1) * (zR ^ 2 - 1) = 0 := by
    linear_combination -hunitC
  rcases mul_eq_zero.mp hfactor with hL | hR
  · exact Or.inl (sub_eq_zero.mp hL)
  · exact Or.inr (sub_eq_zero.mp hR)

end

end Hadamard6
