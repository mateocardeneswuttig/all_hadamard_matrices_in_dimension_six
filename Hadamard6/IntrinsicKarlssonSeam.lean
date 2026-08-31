import Hadamard6.H2ExceptionalSeamDiagonal

/-!
# Internal closure of the intrinsic Karlsson seam

This module discharges the last residual seam statement left by the intrinsic
`H₂` normalization.  It proves the raw-or-seam coverage predicate consumed
by the finite-corner certificate, with no published coverage hypothesis.
-/

namespace Hadamard6

noncomputable section

private theorem standardOmega_square_isPrimitive :
    IsPrimitiveCubicPhase (standardOmega ^ 2) := by
  have homega := standardOmega_isPrimitiveCubicPhase
  have hcube : standardOmega ^ 3 = 1 :=
    primitiveCubicPhase_cube homega
  have hfourth : (standardOmega ^ 2) ^ 2 = standardOmega := by
    calc
      (standardOmega ^ 2) ^ 2 =
          standardOmega * standardOmega ^ 3 := by ring
      _ = standardOmega := by rw [hcube, mul_one]
  refine ⟨primitiveCubicPhase_sq_norm homega, ?_⟩
  rw [hfourth]
  linear_combination homega.2

private theorem standardOmega_square_square_smul :
    (standardOmega ^ 2) ^ 2 • karlssonF2 =
      standardOmega • karlssonF2 := by
  have hcube := primitiveCubicPhase_cube
    standardOmega_isPrimitiveCubicPhase
  have hfourth : (standardOmega ^ 2) ^ 2 = standardOmega := by
    calc
      (standardOmega ^ 2) ^ 2 =
          standardOmega * standardOmega ^ 3 := by ring
      _ = standardOmega := by rw [hcube, mul_one]
  rw [hfourth]

theorem intrinsicKarlssonCommonFourier_isAffineFourierSeam
    {H : Mat6} (hH : IsHadamard H)
    (q : IntrinsicKarlssonCommonFourierPresentation H) :
    IsAffineFourierSeam H := by
  have hRaw : IsHadamard
      (karlssonRawMatrix 1 1 q.z₁ q.z₂ q.z₃ q.z₄) :=
    (equivalent_isHadamard_iff q.equivalent_raw).1 hH
  have hseamRaw := karlssonRaw_one_one_isAffineFourierSeam
    q.z₁_unit q.z₂_unit q.z₃_unit q.z₄_unit hRaw
  exact isAffineFourierSeam_of_equivalent q.equivalent_raw hseamRaw

theorem intrinsicKarlssonExceptional_isAffineFourierSeam
    {H : Mat6} (q : H2ExceptionalCorePresentation H) :
    IsAffineFourierSeam H := by
  rcases q.exceptional with hL | hL | hL | hL
  · have hA := h2ParameterA_eq_omega_f2_of_lambda_one hL
    have hB := h2ParameterB_eq_omega_sq_f2_of_A_eq_omega_f2
      (h2ParameterA_add_h2ParameterB q.normalized.canonical) hA
    exact isAffineFourierSeam_of_equivalent q.equivalent
      (h2_scalar_core_isAffineFourierSeam q.normalized
        standardOmega_isPrimitiveCubicPhase hA hB)
  · have hA := h2ParameterA_eq_omega_sq_f2_of_lambda_neg_one hL
    have hB := h2ParameterB_eq_omega_f2_of_A_eq_omega_sq_f2
      (h2ParameterA_add_h2ParameterB q.normalized.canonical) hA
    have hB' :
        h2ParameterB q.K =
          (standardOmega ^ 2) ^ 2 • karlssonF2 := by
      rw [hB, standardOmega_square_square_smul]
    exact isAffineFourierSeam_of_equivalent q.equivalent
      (h2_scalar_core_isAffineFourierSeam q.normalized
        standardOmega_square_isPrimitive hA hB')
  · exact isAffineFourierSeam_of_equivalent q.equivalent
      (h2_diagonal_core_isAffineFourierSeam q.normalized (Or.inl hL))
  · exact isAffineFourierSeam_of_equivalent q.equivalent
      (h2_diagonal_core_isAffineFourierSeam q.normalized (Or.inr hL))

/-- The residual seam predicate from the intrinsic `H₂` extraction is now
proved internally. -/
theorem intrinsicKarlssonSeamIdentification_proved :
    IntrinsicKarlssonSeamIdentification := by
  constructor
  · intro H hH hq
    rcases hq with ⟨q⟩
    exact intrinsicKarlssonCommonFourier_isAffineFourierSeam hH q
  · intro H _ hq
    rcases hq with ⟨q⟩
    exact intrinsicKarlssonExceptional_isAffineFourierSeam q

/-- Unconditional raw-or-seam coverage for every `H₂`-reducible order-six
Hadamard matrix. -/
theorem karlssonRawOrSeamCoverage_proved :
    KarlssonRawOrSeamCoverage :=
  karlssonRawOrSeamCoverage_of_intrinsic_seam
    intrinsicKarlssonSeamIdentification_proved

end

end Hadamard6
