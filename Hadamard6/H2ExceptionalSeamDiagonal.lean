import Hadamard6.H2ExceptionalSeamScalarEquivalence

/-!
# Diagonal intrinsic cores reduce to the common Fourier point

Transposition changes a right-diagonal Fourier core into the left-diagonal
core at `t = 1`.  The two signs give `p = 1` and `p = -1`; the latter is
the already-verified raw phase-orientation equivalence.
-/

namespace Hadamard6

noncomputable section

theorem karlssonCoreA_one_neg_one :
    karlssonCoreA 1 (-1) =
      !![standardOmega ^ 2, standardOmega ^ 2;
         standardOmega, -standardOmega] := by
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

private theorem normSq_one_div_local
    {z : ℂ} (hz : Complex.normSq z = 1) :
    Complex.normSq (1 / z) = 1 := by
  rw [one_div_eq_star_of_normSq_eq_one hz]
  simpa [Complex.star_def] using hz

private theorem equivalent_transpose_diagonal {H K : Mat6}
    (hHK : Equivalent H K) : Equivalent H.transpose K.transpose := by
  rcases hHK with ⟨σ, τ, r, c, hr, hc, hpres⟩
  refine ⟨τ, σ, c, r, hc, hr, ?_⟩
  intro i j
  simp only [Matrix.transpose_apply]
  rw [hpres]
  ring

theorem isAffineFourierSeam_of_transpose
    {K : Mat6} (hK : IsAffineFourierSeam K.transpose) :
    IsAffineFourierSeam K := by
  rcases hK with ⟨omega, z₁, z₂, homega, hz₁, hz₂, heq | heq⟩
  · have ht := equivalent_transpose_diagonal heq
    exact ⟨omega, z₁, z₂, homega, hz₁, hz₂,
      Or.inr (by simpa using ht)⟩
  · have ht := equivalent_transpose_diagonal heq
    exact ⟨omega, z₁, z₂, homega, hz₁, hz₂,
      Or.inl (by simpa using ht)⟩

theorem h2_diagonal_core_isAffineFourierSeam
    {K : Mat6} (h : H2BlockNormalizedPresentation K)
    (hL : h2KarlssonLambda (h2ParameterA K) = karlssonSign2 ∨
      h2KarlssonLambda (h2ParameterA K) = -karlssonSign2) :
    IsAffineFourierSeam K := by
  have hT : H2BlockNormalizedPresentation K.transpose := by
    have ht := h2BlockNormalizedPresentation_of_transpose
      (K := K.transpose) (by simpa using h)
    simpa using ht
  rcases hL with hL | hL
  · have hAraw := h2ParameterA_eq_core_from_lambda hL
    have hAT : h2ParameterA K.transpose = karlssonCoreA 1 1 := by
      have hs3 : (Real.sqrt 3) ^ 2 = 3 :=
        Real.sq_sqrt (by norm_num)
      rw [h2ParameterA_transpose, hAraw, karlssonCoreA_one_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        apply Complex.ext <;>
        norm_num [karlssonF2, karlssonSign2, standardOmega,
          Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, pow_two] <;>
        nlinarith
    have hBT : h2ParameterB K.transpose = karlssonCoreB 1 1 :=
      h2Parameter_eq_karlssonCoreB
        (h2ParameterA_add_h2ParameterB hT.canonical) hAT
    have hrawEq := h2BlockNormalized_eq_karlssonRawMatrix
      hT hAT hBT
    have hRaw : IsHadamard
        (karlssonRawMatrix 1 1
          (h2Z₁ K.transpose) (h2Z₂ K.transpose)
          (h2Z₃ K.transpose) (h2Z₄ K.transpose)) := by
      rw [← hrawEq]
      exact hT.canonical.hadamard
    have hseamRaw := karlssonRaw_one_one_isAffineFourierSeam
      hT.canonical.z₁_unit hT.canonical.z₂_unit
      hT.canonical.z₃_unit hT.canonical.z₄_unit hRaw
    have hseamT : IsAffineFourierSeam K.transpose := by
      rw [hrawEq]
      exact hseamRaw
    exact isAffineFourierSeam_of_transpose hseamT
  · have hAraw := h2ParameterA_eq_core_from_lambda hL
    have hAT : h2ParameterA K.transpose =
        karlssonCoreA 1 (-1) := by
      have hs3 : (Real.sqrt 3) ^ 2 = 3 :=
        Real.sq_sqrt (by norm_num)
      rw [h2ParameterA_transpose, hAraw, karlssonCoreA_one_neg_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        apply Complex.ext <;>
        norm_num [karlssonF2, karlssonSign2, standardOmega,
          Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, pow_two] <;>
        nlinarith
    have hBT : h2ParameterB K.transpose = karlssonCoreB 1 (-1) :=
      h2Parameter_eq_karlssonCoreB
        (h2ParameterA_add_h2ParameterB hT.canonical) hAT
    have hrawEq := h2BlockNormalized_eq_karlssonRawMatrix
      hT hAT hBT
    let z₁ := h2Z₁ K.transpose
    let z₂ := h2Z₂ K.transpose
    let z₃ := h2Z₃ K.transpose
    let z₄ := h2Z₄ K.transpose
    have heqNeg : Equivalent
        (karlssonRawMatrix 1 (-1) z₁ z₂ z₃ z₄)
        (karlssonRawMatrix 1 1 z₁ z₂ (1 / z₃) (1 / z₄)) := by
      simpa using equivalent_karlssonRawMatrix_neg_phase
        (t := 1) (p := -1) (z₁ := z₁) (z₂ := z₂)
        (z₃ := z₃) (z₄ := z₄)
        hT.canonical.z₃_unit hT.canonical.z₄_unit
    have hRawNeg : IsHadamard
        (karlssonRawMatrix 1 (-1) z₁ z₂ z₃ z₄) := by
      rw [← hrawEq]
      exact hT.canonical.hadamard
    have hRawOne : IsHadamard
        (karlssonRawMatrix 1 1 z₁ z₂ (1 / z₃) (1 / z₄)) :=
      isHadamard_of_equivalent heqNeg hRawNeg
    have hseamOne := karlssonRaw_one_one_isAffineFourierSeam
      hT.canonical.z₁_unit hT.canonical.z₂_unit
      (normSq_one_div_local hT.canonical.z₃_unit)
      (normSq_one_div_local hT.canonical.z₄_unit) hRawOne
    have hseamNeg :=
      isAffineFourierSeam_of_equivalent heqNeg hseamOne
    have hseamT : IsAffineFourierSeam K.transpose := by
      rw [hrawEq]
      exact hseamNeg
    exact isAffineFourierSeam_of_transpose hseamT

end

end Hadamard6
