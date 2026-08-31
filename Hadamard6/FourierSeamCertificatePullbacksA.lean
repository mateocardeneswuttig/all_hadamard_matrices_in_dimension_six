import Hadamard6.FourierSeamCertificatePullbackB0

namespace Hadamard6

noncomputable section

/-- On the unit torus, every zero of the `B3` endpoint polynomial is
already a zero of the lower-degree `B0` endpoint polynomial.  This is the
reciprocal-conjugate symmetry of the two companion factors. -/
theorem seamP_B0_eq_zero_of_seamP_B3_eq_zero {z₁ z₂ : ℂ}
    (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1)
    (h : seamP_B3 z₁ z₂ = 0) :
    seamP_B0 z₁ z₂ = 0 := by
  let u := z₁ * z₂ + z₁ + z₂
  let v := standardOmega ^ 2 * z₁ + standardOmega * z₂ + 1
  change u ^ 2 * v = 0 at h
  rcases mul_eq_zero.mp h with hu | hv
  · have hu0 : u = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hu
    simp [seamP_B0, u, hu0]
  · have hz₁0 : z₁ ≠ 0 := ne_zero_of_normSq_eq_one hz₁
    have hz₂0 : z₂ ≠ 0 := ne_zero_of_normSq_eq_one hz₂
    have hs₁ : (starRingEnd ℂ) z₁ = 1 / z₁ :=
      (one_div_eq_star_of_normSq_eq_one hz₁).symm
    have hs₂ : (starRingEnd ℂ) z₂ = 1 / z₂ :=
      (one_div_eq_star_of_normSq_eq_one hz₂).symm
    have homega := standardOmega_isPrimitiveCubicPhase
    have hsω : (starRingEnd ℂ) standardOmega = standardOmega ^ 2 :=
      primitiveCubicPhase_star homega
    have hsω2 : (starRingEnd ℂ) (standardOmega ^ 2) = standardOmega := by
      rw [map_pow, hsω]
      calc
        (standardOmega ^ 2) ^ 2 =
            standardOmega * standardOmega ^ 3 := by ring
        _ = standardOmega := by
          rw [primitiveCubicPhase_cube homega, mul_one]
    have hvstar : (starRingEnd ℂ) v = 0 := by rw [hv, map_zero]
    have hw : z₁ * z₂ + standardOmega ^ 2 * z₁ +
        standardOmega * z₂ = 0 := by
      have hscaled := congrArg (fun q : ℂ ↦ z₁ * z₂ * q) hvstar
      dsimp [v] at hscaled
      simp [map_add, map_mul, hs₁, hs₂, hsω, hsω2] at hscaled
      field_simp [hz₁0, hz₂0] at hscaled
      rcases hscaled with (hz | hz) | hscaled
      · exact (hz₁0 hz).elim
      · exact (hz₂0 hz).elim
      · simp only [mul_zero, zero_mul] at hscaled
        linear_combination hscaled
    simp [seamP_B0, hw]

end

end Hadamard6
