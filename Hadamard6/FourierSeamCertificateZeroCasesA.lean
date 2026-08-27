import Hadamard6.FourierSeamCertificatePullbacks

namespace Hadamard6

noncomputable section

theorem determinant_equations_exceptional {x y : ℝ}
    (hsum : x + y = 0)
    (hq : x * y + s3 * (x - y) / 2 = 0) :
    FirstSeamExceptional x y := by
  have hy : y = -x := by linarith
  have hfactor : x * (x - s3) = 0 := by
    calc
      x * (x - s3) =
          -(x * y + s3 * (x - y) / 2) := by rw [hy]; ring
      _ = 0 := by rw [hq]; ring
  rcases mul_eq_zero.mp hfactor with hx | hx
  · exact Or.inl ⟨hx, by linarith⟩
  · have hxs : x = s3 := sub_eq_zero.mp hx
    exact Or.inr (Or.inl ⟨hxs, by rw [hxs] at hsum; linarith⟩)

theorem firstSeam_detE_zero_cases {x y : ℝ}
    (h : (Matrix.toBlocks₁₁
      (firstSeamChart standardOmega (seamCayley x) (seamCayley y))).det = 0) :
    FirstSeamExceptional x y := by
  have hid := firstSeam_detE_cayley_clear x y
  rw [h, mul_zero] at hid
  have hmk : (0 : ℂ) =
      ⟨-s3 * (x + y),
        2 * s3 * (x * y + s3 * (x - y) / 2)⟩ := by
    convert hid using 1
    all_goals apply Complex.ext
    all_goals simp [Complex.mul_re, Complex.mul_im]
  have hre := congrArg Complex.re hmk
  have him := congrArg Complex.im hmk
  have hsum : x + y = 0 := by
    change 0 = -s3 * (x + y) at hre
    have := (mul_eq_zero.mp hre.symm).resolve_left (by nlinarith [s3_pos])
    linarith
  have hq : x * y + s3 * (x - y) / 2 = 0 := by
    change 0 = 2 * s3 * (x * y + s3 * (x - y) / 2) at him
    rcases mul_eq_zero.mp him.symm with hleft | hq
    · rcases mul_eq_zero.mp hleft with htwo | hs
      · norm_num at htwo
      · exact (ne_of_gt s3_pos hs).elim
    · exact hq
  exact determinant_equations_exceptional hsum hq

theorem firstSeam_detB_zero_cases {x y : ℝ}
    (h : (Matrix.toBlocks₁₂
      (firstSeamChart standardOmega (seamCayley x) (seamCayley y))).det = 0) :
    FirstSeamExceptional x y := by
  have hid := firstSeam_detB_cayley_clear x y
  rw [h, mul_zero] at hid
  have hmk : (0 : ℂ) =
      ⟨s3 * (x + y),
        -(2 * s3 * (x * y + s3 * (x - y) / 2))⟩ := by
    convert hid using 1
    all_goals apply Complex.ext
    all_goals simp [Complex.mul_re, Complex.mul_im]
  have hre := congrArg Complex.re hmk
  have him := congrArg Complex.im hmk
  have hsum : x + y = 0 := by
    change 0 = s3 * (x + y) at hre
    exact (mul_eq_zero.mp hre.symm).resolve_left (ne_of_gt s3_pos)
  have hq : x * y + s3 * (x - y) / 2 = 0 := by
    change 0 = -(2 * s3 * (x * y + s3 * (x - y) / 2)) at him
    have hz : 2 * s3 * (x * y + s3 * (x - y) / 2) = 0 := by linarith
    rcases mul_eq_zero.mp hz with hleft | hq
    · rcases mul_eq_zero.mp hleft with htwo | hs
      · norm_num at htwo
      · exact (ne_of_gt s3_pos hs).elim
    · exact hq
  exact determinant_equations_exceptional hsum hq

theorem firstSeam_detC_zero_cases {x y : ℝ}
    (h : (Matrix.toBlocks₂₁
      (firstSeamChart standardOmega (seamCayley x) (seamCayley y))).det = 0) :
    FirstSeamExceptional x y := by
  have hid := firstSeam_detC_cayley_clear x y
  rw [h, mul_zero] at hid
  have hmk : (0 : ℂ) =
      ⟨s3 * (x + y),
        2 * s3 * (x * y + s3 * (x - y) / 2)⟩ := by
    convert hid using 1
    all_goals apply Complex.ext
    all_goals simp [Complex.mul_re, Complex.mul_im]
  have hre := congrArg Complex.re hmk
  have him := congrArg Complex.im hmk
  have hsum : x + y = 0 := by
    change 0 = s3 * (x + y) at hre
    exact (mul_eq_zero.mp hre.symm).resolve_left (ne_of_gt s3_pos)
  have hq : x * y + s3 * (x - y) / 2 = 0 := by
    change 0 = 2 * s3 * (x * y + s3 * (x - y) / 2) at him
    rcases mul_eq_zero.mp him.symm with hleft | hq
    · rcases mul_eq_zero.mp hleft with htwo | hs
      · norm_num at htwo
      · exact (ne_of_gt s3_pos hs).elim
    · exact hq
  exact determinant_equations_exceptional hsum hq

theorem low_endpoint_cases_of_AQ
    {x y : ℝ} (h : seamA x y * seamQminus x y = 0) :
    FirstSeamExceptional x y := by
  rcases mul_eq_zero.mp h with hA | hQ
  · rcases seamA_zero_cases hA with hp | hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hp))
  · rcases seamQminus_zero_cases hQ with hp | hp
    · exact Or.inl hp
    · exact Or.inr (Or.inr (Or.inl hp))

theorem seamP_B0_zero_cases {x y : ℝ}
    (h : seamP_B0 (seamCayley x) (seamCayley y) = 0) :
    FirstSeamExceptional x y := by
  have hid := seamP_B0_pullback_norm x y
  rw [h, mul_zero, Complex.normSq_zero] at hid
  have hprod : seamA x y * seamQminus x y = 0 := by nlinarith
  exact low_endpoint_cases_of_AQ hprod

theorem seamP_B3_zero_cases {x y : ℝ}
    (h : seamP_B3 (seamCayley x) (seamCayley y) = 0) :
    FirstSeamExceptional x y := by
  apply seamP_B0_zero_cases
  exact seamP_B0_eq_zero_of_seamP_B3_eq_zero
    (seamCayley_normSq x) (seamCayley_normSq y) h

theorem seamP_Bswap0_zero_cases {x y : ℝ}
    (h : seamP_Bswap0 (seamCayley x) (seamCayley y) = 0) :
    FirstSeamExceptional x y := by
  rw [seamP_Bswap0_factor] at h
  rcases mul_eq_zero.mp h with hu | hc
  · apply seamP_B0_zero_cases
    have hu0 : seamCayley x * seamCayley y + seamCayley x +
        seamCayley y = 0 := neg_eq_zero.mp hu
    simp [seamP_B0, hu0]
  · have hid := seamP_Bswap0Companion_pullback_norm x y
    rw [hc, mul_zero, Complex.normSq_zero] at hid
    have hQsq : seamQminus x y ^ 2 = 0 := by nlinarith
    have hQ : seamQminus x y = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hQsq
    exact low_endpoint_cases_of_AQ (mul_eq_zero.mpr (Or.inr hQ))

set_option maxHeartbeats 1000000 in
-- Exact nonlinear elimination on this seam branch needs the enlarged budget.
theorem seamP_C0_zero_cases {x y : ℝ}
    (h : seamP_C0 (seamCayley x) (seamCayley y) = 0) :
    FirstSeamExceptional x y := by
  have hid := seamP_C0_pullback x y
  rw [h, mul_zero] at hid
  have hre := congrArg Complex.re hid
  have him := congrArg Complex.im hid
  have hRfull :
      2 * s3 * y * (x + s3) * (y + s3) * seamLminus x y = 0 := by
    exact hre.symm
  have hIfull :
      2 * (y - s3) ^ 2 * (x ^ 2 * y + 2 * x - y) = 0 := by
    exact him.symm
  have hR :
      y = 0 ∨ x + s3 = 0 ∨ y + s3 = 0 ∨ seamLminus x y = 0 := by
    rcases mul_eq_zero.mp hRfull with hleft | hL
    · rcases mul_eq_zero.mp hleft with hleft | hys
      · rcases mul_eq_zero.mp hleft with hleft | hxs
        · rcases mul_eq_zero.mp hleft with hleft | hy
          · rcases mul_eq_zero.mp hleft with htwo | hs
            · norm_num at htwo
            · exact (ne_of_gt s3_pos hs).elim
          · exact Or.inl hy
        · exact Or.inr (Or.inl hxs)
      · exact Or.inr (Or.inr (Or.inl hys))
    · exact Or.inr (Or.inr (Or.inr hL))
  have hI : y = s3 ∨ x ^ 2 * y + 2 * x - y = 0 := by
    rcases mul_eq_zero.mp hIfull with hrest | hM
    · rcases mul_eq_zero.mp hrest with htwo | hy
      · norm_num at htwo
      · left
        have : y - s3 = 0 := (sq_eq_zero_iff.mp hy)
        linarith
    · exact Or.inr hM
  rcases hR with hy0 | hR
  · have hM : x ^ 2 * y + 2 * x - y = 0 :=
      hI.resolve_left (by intro hys; linarith [s3_pos])
    exact Or.inl ⟨by nlinarith [hM], hy0⟩
  rcases hR with hxs | hR
  · have hx : x = -s3 := by linarith
    have hy : y = s3 := by
      rcases hI with hy | hM
      · exact hy
      · rw [hx] at hM
        have hneg : (-s3) ^ 2 = 3 := by nlinarith [s3_sq]
        rw [hneg] at hM
        linarith
    exact Or.inr (Or.inr (Or.inl ⟨hx, hy⟩))
  rcases hR with hys | hL
  · have hy : y = -s3 := by linarith
    have hM : x ^ 2 * y + 2 * x - y = 0 :=
      hI.resolve_left (by intro h; linarith [s3_pos])
    have hfactor : (x - s3) * (x + s3 / 3) = 0 := by
      rw [hy] at hM
      have hidf :
          -s3 * ((x - s3) * (x + s3 / 3)) =
            x ^ 2 * (-s3) + 2 * x - (-s3) := by
        ring_nf
        rw [s3_sq, s3_pow3]
        ring
      have hz : -s3 * ((x - s3) * (x + s3 / 3)) = 0 := by
        rw [hidf, hM]
      exact (mul_eq_zero.mp hz).resolve_left (by nlinarith [s3_pos])
    rcases mul_eq_zero.mp hfactor with hx | hx
    · exact Or.inr (Or.inl ⟨by linarith, hy⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, hy⟩)))
  · rcases hI with hy | hM
    · have hx : x = -s3 := by
        simp [seamLminus, hy] at hL
        nlinarith [s3_sq]
      exact Or.inr (Or.inr (Or.inl ⟨hx, hy⟩))
    · have hres :
          y * (-(s3 / 3) * (x + s3) * (x ^ 2 + 1)) = 0 := by
        have hcomb :
            (-2 * x) * seamLminus x y +
              (1 - s3 * x / 3) * (x ^ 2 * y + 2 * x - y) = 0 := by
          rw [hL, hM]
          ring
        calc
          y * (-(s3 / 3) * (x + s3) * (x ^ 2 + 1)) =
              (-2 * x) * seamLminus x y +
                (1 - s3 * x / 3) * (x ^ 2 * y + 2 * x - y) := by
            simp [seamLminus]
            ring_nf
            rw [s3_sq]
            ring
          _ = 0 := hcomb
      rcases mul_eq_zero.mp hres with hy0 | hprod
      · simp [seamLminus, hy0] at hL hM
        nlinarith [s3_pos]
      · have hx : x = -s3 := by
          rcases mul_eq_zero.mp hprod with hleft | hpos
          · rcases mul_eq_zero.mp hleft with hs | hx
            · exact (ne_of_gt s3_pos (by nlinarith [hs] : s3 = 0)).elim
            · linarith
          · nlinarith [sq_nonneg x]
        have hy : y = s3 := by
          simp [seamLminus, hx] at hL
          nlinarith [s3_sq]
        exact Or.inr (Or.inr (Or.inl ⟨hx, hy⟩))

set_option maxHeartbeats 1000000 in
-- Exact nonlinear elimination on this seam branch needs the enlarged budget.

end

end Hadamard6
