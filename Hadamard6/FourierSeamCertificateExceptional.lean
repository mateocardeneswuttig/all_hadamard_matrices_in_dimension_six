import Hadamard6.FourierSeamCertificateZeroCasesB

namespace Hadamard6

noncomputable section

theorem exceptional00_corner21 :
    leadingFiniteCornerWitnessProduct
      (seamCornerChart (2 : I3) (1 : I2)
        (affineFourierMatrix standardOmega 1 1)) ≠ 0 := by
  intro h
  change leadingFiniteCornerWitnessProduct
    (dephase (reindexMatrix seamRows025 seamColumns025
      (affineFourierMatrix standardOmega 1 1))) = 0 at h
  close_standard_seam_corner h

set_option maxHeartbeats 1000000 in
-- The exact exceptional-corner normalization needs the enlarged budget.
set_option maxRecDepth 100000 in
theorem exceptional_s_neg_s_corner11 :
    leadingFiniteCornerWitnessProduct
      (seamCornerChart (1 : I3) (1 : I2)
        (affineFourierMatrix standardOmega standardOmega
          (standardOmega ^ 2))) ≠ 0 := by
  intro h
  change leadingFiniteCornerWitnessProduct
    (dephase (reindexMatrix seamRows013 seamColumns025
      (affineFourierMatrix standardOmega standardOmega
        (standardOmega ^ 2)))) = 0 at h
  close_standard_seam_corner h

set_option maxHeartbeats 1000000 in
-- The exact exceptional-corner normalization needs the enlarged budget.
set_option maxRecDepth 100000 in
theorem exceptional_neg_s_s_corner01 :
    leadingFiniteCornerWitnessProduct
      (seamCornerChart (0 : I3) (1 : I2)
        (affineFourierMatrix standardOmega (standardOmega ^ 2)
          standardOmega)) ≠ 0 := by
  intro h
  change leadingFiniteCornerWitnessProduct
    (dephase (reindexMatrix seamRows012 seamColumns025
      (affineFourierMatrix standardOmega (standardOmega ^ 2)
        standardOmega))) = 0 at h
  close_standard_seam_corner h

set_option maxHeartbeats 1000000 in
-- The exact exceptional-corner normalization needs the enlarged budget.
set_option maxRecDepth 100000 in
theorem exceptional_neg_third_s_neg_s_corner10 :
    leadingFiniteCornerWitnessProduct
      (seamCornerChart (1 : I3) (0 : I2)
        (affineFourierMatrix standardOmega (-standardOmega)
          (standardOmega ^ 2))) ≠ 0 := by
  intro h
  change leadingFiniteCornerWitnessProduct
    (dephase (reindexMatrix seamRows013 seamColumns024
      (affineFourierMatrix standardOmega (-standardOmega)
        (standardOmega ^ 2)))) = 0 at h
  close_standard_seam_corner h

set_option maxHeartbeats 1000000 in
-- The exact exceptional-corner normalization needs the enlarged budget.
set_option maxRecDepth 100000 in
theorem exceptional_neg_third_s_third_s_corner10 :
    leadingFiniteCornerWitnessProduct
      (seamCornerChart (1 : I3) (0 : I2)
        (affineFourierMatrix standardOmega (-standardOmega)
          (-(standardOmega ^ 2)))) ≠ 0 := by
  intro h
  change leadingFiniteCornerWitnessProduct
    (dephase (reindexMatrix seamRows013 seamColumns024
      (affineFourierMatrix standardOmega (-standardOmega)
        (-(standardOmega ^ 2))))) = 0 at h
  close_standard_seam_corner h

set_option maxHeartbeats 1000000 in
-- The exact exceptional-corner normalization needs the enlarged budget.
set_option maxRecDepth 100000 in
theorem exceptional_s_third_s_corner10 :
    leadingFiniteCornerWitnessProduct
      (seamCornerChart (1 : I3) (0 : I2)
        (affineFourierMatrix standardOmega standardOmega
          (-(standardOmega ^ 2)))) ≠ 0 := by
  intro h
  change leadingFiniteCornerWitnessProduct
    (dephase (reindexMatrix seamRows013 seamColumns024
      (affineFourierMatrix standardOmega standardOmega
        (-(standardOmega ^ 2))))) = 0 at h
  close_standard_seam_corner h

set_option maxHeartbeats 1000000 in
-- The exact exceptional-corner normalization needs the enlarged budget.
set_option maxRecDepth 100000 in
theorem boundary_neg_one_neg_omega_sq_corner10 :
    leadingFiniteCornerWitnessProduct
      (seamCornerChart (1 : I3) (0 : I2)
        (affineFourierMatrix standardOmega (-1)
          (-(standardOmega ^ 2)))) ≠ 0 := by
  intro h
  change leadingFiniteCornerWitnessProduct
    (dephase (reindexMatrix seamRows013 seamColumns024
      (affineFourierMatrix standardOmega (-1)
        (-(standardOmega ^ 2))))) = 0 at h
  close_standard_seam_corner h

set_option maxHeartbeats 1000000 in
-- The exact exceptional-corner normalization needs the enlarged budget.
set_option maxRecDepth 100000 in
theorem boundary_neg_omega_neg_one_corner10 :
    leadingFiniteCornerWitnessProduct
      (seamCornerChart (1 : I3) (0 : I2)
        (affineFourierMatrix standardOmega (-standardOmega) (-1))) ≠ 0 := by
  intro h
  change leadingFiniteCornerWitnessProduct
    (dephase (reindexMatrix seamRows013 seamColumns024
      (affineFourierMatrix standardOmega (-standardOmega) (-1)))) = 0 at h
  close_standard_seam_corner h

/-- Away from the projective point `-1`, the first corner either works or
its exact zero classification selects one row of the six-point table. -/
theorem standard_cayley_six_corner_certificate (x y : ℝ) :
    ∃ r : I3, ∃ c : I2,
      leadingFiniteCornerWitnessProduct
        (seamCornerChart r c
          (affineFourierMatrix standardOmega
            (seamCayley x) (seamCayley y))) ≠ 0 := by
  by_cases hfirst : leadingFiniteCornerWitnessProduct
      (firstSeamChart standardOmega (seamCayley x) (seamCayley y)) ≠ 0
  · refine ⟨0, 0, ?_⟩
    rw [seamCornerChart_zero_zero_eq standardOmega_isPrimitiveCubicPhase
      (seamCayley_normSq x) (seamCayley_normSq y)]
    exact hfirst
  · have hexceptional := firstSeam_witness_zero_cases
      (not_ne_iff.mp hfirst)
    rcases hexceptional with h00 | hsns | hnss | hns3ns | hns3s3 | hss3
    · rcases h00 with ⟨rfl, rfl⟩
      refine ⟨2, 1, ?_⟩
      simpa [seamCayley_zero] using exceptional00_corner21
    · rcases hsns with ⟨rfl, rfl⟩
      refine ⟨1, 1, ?_⟩
      simpa [seamCayley_s3, seamCayley_neg_s3] using
        exceptional_s_neg_s_corner11
    · rcases hnss with ⟨rfl, rfl⟩
      refine ⟨0, 1, ?_⟩
      simpa [seamCayley_s3, seamCayley_neg_s3] using
        exceptional_neg_s_s_corner01
    · rcases hns3ns with ⟨rfl, rfl⟩
      refine ⟨1, 0, ?_⟩
      simpa [seamCayley_neg_third_s3, seamCayley_neg_s3] using
        exceptional_neg_third_s_neg_s_corner10
    · rcases hns3s3 with ⟨rfl, rfl⟩
      refine ⟨1, 0, ?_⟩
      simpa [seamCayley_neg_third_s3, seamCayley_third_s3] using
        exceptional_neg_third_s_third_s_corner10
    · rcases hss3 with ⟨rfl, rfl⟩
      refine ⟨1, 0, ?_⟩
      simpa [seamCayley_s3, seamCayley_third_s3] using
        exceptional_s_third_s_corner10

theorem standard_nonboundary_six_corner_certificate
    {z₁ z₂ : ℂ} (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1) (hz₁m : z₁ ≠ -1)
    (hz₂m : z₂ ≠ -1) :
    ∃ r : I3, ∃ c : I2,
      leadingFiniteCornerWitnessProduct
        (seamCornerChart r c
          (affineFourierMatrix standardOmega z₁ z₂)) ≠ 0 := by
  rcases exists_seamCayley_of_normSq_one hz₁ hz₁m with ⟨x, rfl⟩
  rcases exists_seamCayley_of_normSq_one hz₂ hz₂m with ⟨y, rfl⟩
  exact standard_cayley_six_corner_certificate x y

end

end Hadamard6
