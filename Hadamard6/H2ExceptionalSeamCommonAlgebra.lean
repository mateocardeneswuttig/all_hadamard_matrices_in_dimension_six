import Hadamard6.H2ExceptionalSeamAlgebra

/-!
# The common Fourier point in intrinsic `H₂` coordinates

At the remaining raw point `t = p = 1`, the two inverse-Fourier cores are
left-diagonal Fourier matrices.  The four unit central blocks then force the
small phase alternatives used to identify the affine-Fourier seam.
-/

namespace Hadamard6

noncomputable section

theorem karlssonCoreA_one_one :
    karlssonCoreA 1 1 =
      !![standardOmega, standardOmega;
         standardOmega ^ 2, -(standardOmega ^ 2)] := by
  have hs3 : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [karlssonCoreA, karlssonLambda, karlssonHalfAngleU,
      karlssonHalfAngleV, karlssonF2, standardOmega,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im, pow_two] <;>
    nlinarith

theorem karlssonCoreB_one_one :
    karlssonCoreB 1 1 =
      !![standardOmega ^ 2, standardOmega ^ 2;
         standardOmega, -standardOmega] := by
  rw [karlssonCoreB, karlssonCoreA_one_one]
  have hsum : 1 + standardOmega + standardOmega ^ 2 = 0 := by
    linear_combination standardOmega_isPrimitiveCubicPhase.2
  have hsquare : standardOmega ^ 2 = -1 - standardOmega := by
    linear_combination hsum
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [karlssonF2, hsquare]

/-- At the common Fourier point, a unit entry in an `A`-block forces the
right phase to be a sign or the square of the left phase to be `ω`. -/
theorem commonCoreA_unit_forces_phase_alternative
    {zL zR : ℂ}
    (hzL : Complex.normSq zL = 1)
    (hzR : Complex.normSq zR = 1)
    (hunit : Complex.normSq
      (karlssonBlockProduct zL (karlssonCoreA 1 1) zR 0 0) = 1) :
    zR ^ 2 = 1 ∨ zL ^ 2 = standardOmega := by
  have hω0 := primitiveCubicPhase_ne_zero
    standardOmega_isPrimitiveCubicPhase
  have hzL0 := ne_zero_of_normSq_eq_one hzL
  have hzR0 := ne_zero_of_normSq_eq_one hzR
  have hsω : (starRingEnd ℂ) standardOmega = standardOmega ^ 2 :=
    primitiveCubicPhase_star standardOmega_isPrimitiveCubicPhase
  have hsL : (starRingEnd ℂ) zL = 1 / zL :=
    (one_div_eq_star_of_normSq_eq_one hzL).symm
  have hsR : (starRingEnd ℂ) zR = 1 / zR :=
    (one_div_eq_star_of_normSq_eq_one hzR).symm
  have hunitC :
      ((Complex.normSq
        (karlssonBlockProduct zL (karlssonCoreA 1 1) zR 0 0) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hunit
  rw [karlssonCoreA_one_one] at hunitC
  simp [karlssonBlockProduct, karlssonZLeft, karlssonZRight,
    Complex.normSq_eq_conj_mul_self,
    map_add, map_mul, hsω, hsL, hsR] at hunitC
  field_simp [hω0, hzL0, hzR0] at hunitC
  have hsum : 1 + standardOmega + standardOmega ^ 2 = 0 := by
    linear_combination standardOmega_isPrimitiveCubicPhase.2
  have hcube : standardOmega ^ 3 = 1 :=
    primitiveCubicPhase_cube standardOmega_isPrimitiveCubicPhase
  have hsquare : standardOmega ^ 2 = -1 - standardOmega := by
    linear_combination hsum
  rw [hcube, one_mul, hsquare] at hunitC
  have hfactor :
      (zR ^ 2 - 1) * (zL ^ 2 - standardOmega) = 0 := by
    have hscaled : standardOmega *
        ((zR ^ 2 - 1) * (zL ^ 2 - standardOmega)) = 0 := by
      linear_combination -hunitC +
        (zR - 1) * (zL * zR - zL - zR - 1) * hsum
    exact (mul_eq_zero.mp hscaled).resolve_left hω0
  rcases mul_eq_zero.mp hfactor with hR | hL
  · exact Or.inl (sub_eq_zero.mp hR)
  · exact Or.inr (sub_eq_zero.mp hL)

/-- The complementary `B`-block has the conjugate alternative. -/
theorem commonCoreB_unit_forces_phase_alternative
    {zL zR : ℂ}
    (hzL : Complex.normSq zL = 1)
    (hzR : Complex.normSq zR = 1)
    (hunit : Complex.normSq
      (karlssonBlockProduct zL (karlssonCoreB 1 1) zR 0 0) = 1) :
    zR ^ 2 = 1 ∨ zL ^ 2 = standardOmega ^ 2 := by
  have hω0 := primitiveCubicPhase_ne_zero
    standardOmega_isPrimitiveCubicPhase
  have hzL0 := ne_zero_of_normSq_eq_one hzL
  have hzR0 := ne_zero_of_normSq_eq_one hzR
  have hsω : (starRingEnd ℂ) standardOmega = standardOmega ^ 2 :=
    primitiveCubicPhase_star standardOmega_isPrimitiveCubicPhase
  have hsωsq : (starRingEnd ℂ) (standardOmega ^ 2) = standardOmega := by
    rw [map_pow, hsω]
    calc
      (standardOmega ^ 2) ^ 2 =
          standardOmega * standardOmega ^ 3 := by ring
      _ = standardOmega := by
        rw [primitiveCubicPhase_cube standardOmega_isPrimitiveCubicPhase,
          mul_one]
  have hsL : (starRingEnd ℂ) zL = 1 / zL :=
    (one_div_eq_star_of_normSq_eq_one hzL).symm
  have hsR : (starRingEnd ℂ) zR = 1 / zR :=
    (one_div_eq_star_of_normSq_eq_one hzR).symm
  have hunitC :
      ((Complex.normSq
        (karlssonBlockProduct zL (karlssonCoreB 1 1) zR 0 0) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hunit
  rw [karlssonCoreB_one_one] at hunitC
  simp [karlssonBlockProduct, karlssonZLeft, karlssonZRight,
    Complex.normSq_eq_conj_mul_self,
    map_add, map_mul, hsω, hsωsq, hsL, hsR] at hunitC
  field_simp [hω0, hzL0, hzR0] at hunitC
  have hsum : 1 + standardOmega + standardOmega ^ 2 = 0 := by
    linear_combination standardOmega_isPrimitiveCubicPhase.2
  have hfactor :
      (zR ^ 2 - 1) * (zL ^ 2 - standardOmega ^ 2) = 0 := by
    have hscaled : standardOmega ^ 2 *
        ((zR ^ 2 - 1) * (zL ^ 2 - standardOmega ^ 2)) = 0 := by
      linear_combination -hunitC +
        4 * zL * zR * (standardOmega - 1) * hsum
    exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 2 hω0)
  rcases mul_eq_zero.mp hfactor with hR | hL
  · exact Or.inl (sub_eq_zero.mp hR)
  · exact Or.inr (sub_eq_zero.mp hL)

/-- The four central blocks give the complete Boolean phase pattern at the
common point.  This statement uses only entrywise unimodularity. -/
theorem karlssonRaw_one_one_phase_alternatives
    {z₁ z₂ z₃ z₄ : ℂ}
    (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1)
    (hz₃ : Complex.normSq z₃ = 1)
    (hz₄ : Complex.normSq z₄ = 1)
    (hH : IsHadamard (karlssonRawMatrix 1 1 z₁ z₂ z₃ z₄)) :
    (z₁ ^ 2 = 1 ∨ z₃ ^ 2 = standardOmega) ∧
    (z₂ ^ 2 = 1 ∨ z₃ ^ 2 = standardOmega ^ 2) ∧
    (z₁ ^ 2 = 1 ∨ z₄ ^ 2 = standardOmega ^ 2) ∧
    (z₂ ^ 2 = 1 ∨ z₄ ^ 2 = standardOmega) := by
  have hAunit : Complex.normSq
      (karlssonBlockProduct z₃ (karlssonCoreA 1 1) z₁ 0 0) = 1 := by
    simpa [karlssonRawMatrix, reindexMatrix, karlssonMixedChartMatrix,
      karlssonMixedE, karlssonMixedB, karlssonMixedC, karlssonMixedD,
      mixedLeadingBlock, mixedHorizontalBlock,
      h2Tail₀, h2Tail₂] using
      hH.1 h2Tail₀ h2Tail₀
  have hBunit : Complex.normSq
      (karlssonBlockProduct z₃ (karlssonCoreB 1 1) z₂ 0 0) = 1 := by
    simpa [karlssonRawMatrix, reindexMatrix, karlssonMixedChartMatrix,
      karlssonMixedE, karlssonMixedB, karlssonMixedC, karlssonMixedD,
      mixedLeadingBlock, mixedHorizontalBlock,
      h2Tail₀, h2Tail₂] using
      hH.1 h2Tail₀ h2Tail₂
  have hCunit : Complex.normSq
      (karlssonBlockProduct z₄ (karlssonCoreB 1 1) z₁ 0 0) = 1 := by
    simpa [karlssonRawMatrix, reindexMatrix, karlssonMixedChartMatrix,
      karlssonMixedE, karlssonMixedB, karlssonMixedC, karlssonMixedD,
      mixedLeadingBlock, mixedHorizontalBlock,
      h2Tail₀, h2Tail₂] using
      hH.1 h2Tail₂ h2Tail₀
  have hDunit : Complex.normSq
      (karlssonBlockProduct z₄ (karlssonCoreA 1 1) z₂ 0 0) = 1 := by
    simpa [karlssonRawMatrix, reindexMatrix, karlssonMixedChartMatrix,
      karlssonMixedE, karlssonMixedB, karlssonMixedC, karlssonMixedD,
      mixedLeadingBlock, mixedHorizontalBlock,
      h2Tail₀, h2Tail₂] using
      hH.1 h2Tail₂ h2Tail₂
  exact ⟨
    commonCoreA_unit_forces_phase_alternative hz₃ hz₁ hAunit,
    commonCoreB_unit_forces_phase_alternative hz₃ hz₂ hBunit,
    commonCoreB_unit_forces_phase_alternative hz₄ hz₁ hCunit,
    commonCoreA_unit_forces_phase_alternative hz₄ hz₂ hDunit⟩

end

end Hadamard6
