import Hadamard6.FourierSeamCertificateZeroCasesA

namespace Hadamard6

noncomputable section

theorem seamP_C3_zero_cases {x y : ℝ}
    (h : seamP_C3 (seamCayley x) (seamCayley y) = 0) :
    FirstSeamExceptional x y := by
  have hid := seamP_C3_pullback x y
  rw [h, mul_zero] at hid
  have hre := congrArg Complex.re hid
  have him := congrArg Complex.im hid
  have hRfull :
      2 * s3 * (x + s3) * (x - y) * (y - s3) * seamLplus x y = 0 :=
    hre.symm
  have hIfull : -(6 * (x + y) * seamLminus x y ^ 2) = 0 :=
    him.symm
  have hR :
      x + s3 = 0 ∨ x - y = 0 ∨ y - s3 = 0 ∨ seamLplus x y = 0 := by
    rcases mul_eq_zero.mp hRfull with hleft | hL
    · rcases mul_eq_zero.mp hleft with hleft | hy
      · rcases mul_eq_zero.mp hleft with hleft | hxy
        · rcases mul_eq_zero.mp hleft with hleft | hx
          · rcases mul_eq_zero.mp hleft with htwo | hs
            · norm_num at htwo
            · exact (ne_of_gt s3_pos hs).elim
          · exact Or.inl hx
        · exact Or.inr (Or.inl hxy)
      · exact Or.inr (Or.inr (Or.inl hy))
    · exact Or.inr (Or.inr (Or.inr hL))
  have hI : x + y = 0 ∨ seamLminus x y = 0 := by
    have hzero : 6 * (x + y) * seamLminus x y ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp hzero with hleft | hLsq
    · rcases mul_eq_zero.mp hleft with hsix | hsum
      · norm_num at hsix
      · exact Or.inl hsum
    · exact Or.inr (sq_eq_zero_iff.mp hLsq)
  rcases hR with hxs | hR
  · have hx : x = -s3 := by linarith
    have hy : y = s3 := by
      rcases hI with hsum | hL
      · linarith
      · have hL' :
            (-s3) * y - s3 * (-s3) / 3 + s3 * y / 3 + 1 = 0 := by
          simpa only [seamLminus, hx] using hL
        have hprod : s3 * (y - s3) = 0 := by nlinarith [hL', s3_sq]
        exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt s3_pos) |> sub_eq_zero.mp
    exact Or.inr (Or.inr (Or.inl ⟨hx, hy⟩))
  rcases hR with hxy | hR
  · have heq : x = y := by linarith
    rcases hI with hsum | hL
    · exact Or.inl ⟨by linarith, by linarith⟩
    · simp [seamLminus, heq] at hL
      nlinarith [sq_nonneg y]
  rcases hR with hys | hLplus
  · have hy : y = s3 := by linarith
    have hx : x = -s3 := by
      rcases hI with hsum | hL
      · linarith
      · have hL' :
            x * s3 - s3 * x / 3 + s3 * s3 / 3 + 1 = 0 := by
          simpa only [seamLminus, hy] using hL
        have hprod : s3 * (x + s3) = 0 := by nlinarith [hL', s3_sq]
        have : x + s3 = 0 :=
          (mul_eq_zero.mp hprod).resolve_left (ne_of_gt s3_pos)
        linarith
    exact Or.inr (Or.inr (Or.inl ⟨hx, hy⟩))
  · rcases hI with hsum | hLminus
    · have hy : y = -x := by linarith
      have hfactor : (x - s3) * (x + s3 / 3) = 0 := by
        have hz : -x ^ 2 + 2 * s3 * x / 3 + 1 = 0 := by
          convert hLplus using 1
          all_goals simp [seamLplus, hy]
          all_goals ring
        have hidf :
            -((x - s3) * (x + s3 / 3)) =
              -x ^ 2 + 2 * s3 * x / 3 + 1 := by
          ring_nf
          rw [s3_sq]
          ring
        have : -((x - s3) * (x + s3 / 3)) = 0 := by rw [hidf, hz]
        linarith
      rcases mul_eq_zero.mp hfactor with hx | hx
      · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      · exact Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl ⟨by linarith, by linarith⟩))))
    · have hxy : x = y := by
        have hdiff : 2 * s3 * (x - y) / 3 = 0 := by
          simp [seamLplus, seamLminus] at hLplus hLminus
          linarith
        have hsne : s3 ≠ 0 := ne_of_gt s3_pos
        have hprod : s3 * (x - y) = 0 := by nlinarith [hdiff]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hsne)
      simp [seamLplus, hxy] at hLplus
      nlinarith [sq_nonneg y]

set_option maxHeartbeats 1000000 in
-- Exact nonlinear elimination on this seam branch needs the enlarged budget.
theorem seamP_Cswap0_zero_cases {x y : ℝ}
    (h : seamP_Cswap0 (seamCayley x) (seamCayley y) = 0) :
    FirstSeamExceptional x y := by
  have hid := seamP_Cswap0_pullback x y
  rw [h, mul_zero] at hid
  have hre := congrArg Complex.re hid
  have him := congrArg Complex.im hid
  have hRfull :
      -(2 * s3 * x * (x - s3) * (y - s3) * seamLminus x y) = 0 :=
    hre.symm
  have hIfull :
      2 * (x + s3) ^ 2 * (x * y ^ 2 - x + 2 * y) = 0 :=
    him.symm
  have hR :
      x = 0 ∨ x - s3 = 0 ∨ y - s3 = 0 ∨ seamLminus x y = 0 := by
    have hz : 2 * s3 * x * (x - s3) * (y - s3) * seamLminus x y = 0 := by
      linarith
    rcases mul_eq_zero.mp hz with hleft | hL
    · rcases mul_eq_zero.mp hleft with hleft | hy
      · rcases mul_eq_zero.mp hleft with hleft | hxS
        · rcases mul_eq_zero.mp hleft with hleft | hx
          · rcases mul_eq_zero.mp hleft with htwo | hs
            · norm_num at htwo
            · exact (ne_of_gt s3_pos hs).elim
          · exact Or.inl hx
        · exact Or.inr (Or.inl hxS)
      · exact Or.inr (Or.inr (Or.inl hy))
    · exact Or.inr (Or.inr (Or.inr hL))
  have hI : x = -s3 ∨ x * y ^ 2 - x + 2 * y = 0 := by
    rcases mul_eq_zero.mp hIfull with hleft | hN
    · rcases mul_eq_zero.mp hleft with htwo | hsq
      · norm_num at htwo
      · left
        have : x + s3 = 0 := sq_eq_zero_iff.mp hsq
        linarith
    · exact Or.inr hN
  rcases hR with hx0 | hR
  · have hN : x * y ^ 2 - x + 2 * y = 0 :=
      hI.resolve_left (by intro hx; linarith [s3_pos])
    exact Or.inl ⟨hx0, by rw [hx0] at hN; linarith⟩
  rcases hR with hxs | hR
  · have hx : x = s3 := by linarith
    have hN : x * y ^ 2 - x + 2 * y = 0 :=
      hI.resolve_left (by intro h; linarith [s3_pos])
    have hfactor : (y + s3) * (y - s3 / 3) = 0 := by
      rw [hx] at hN
      have hidf :
          s3 * ((y + s3) * (y - s3 / 3)) =
            s3 * y ^ 2 - s3 + 2 * y := by
        ring_nf
        rw [s3_sq, s3_pow3]
        ring
      have hz : s3 * ((y + s3) * (y - s3 / 3)) = 0 := by rw [hidf, hN]
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt s3_pos)
    rcases mul_eq_zero.mp hfactor with hy | hy
    · exact Or.inr (Or.inl ⟨hx, by linarith⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hx, by linarith⟩))))
  rcases hR with hys | hL
  · have hy : y = s3 := by linarith
    have hx : x = -s3 := by
      rcases hI with hx | hN
      · exact hx
      · rw [hy] at hN
        rw [s3_sq] at hN
        linarith
    exact Or.inr (Or.inr (Or.inl ⟨hx, hy⟩))
  · rcases hI with hx | hN
    · have hy : y = s3 := by
        simp [seamLminus, hx] at hL
        nlinarith [s3_sq]
      exact Or.inr (Or.inr (Or.inl ⟨hx, hy⟩))
    · have hres :
          x * (s3 / 3 * (y - s3) * (y ^ 2 + 1)) = 0 := by
        have hcomb :
            (-2 * y) * seamLminus x y +
              (s3 * y / 3 + 1) * (x * y ^ 2 - x + 2 * y) = 0 := by
          rw [hL, hN]
          ring
        calc
          x * (s3 / 3 * (y - s3) * (y ^ 2 + 1)) =
              (-2 * y) * seamLminus x y +
                (s3 * y / 3 + 1) * (x * y ^ 2 - x + 2 * y) := by
            simp [seamLminus]
            ring_nf
            rw [s3_sq]
            ring
          _ = 0 := hcomb
      rcases mul_eq_zero.mp hres with hx0 | hprod
      · simp [seamLminus, hx0] at hL hN
        nlinarith [s3_pos]
      · have hy : y = s3 := by
          rcases mul_eq_zero.mp hprod with hleft | hpos
          · rcases mul_eq_zero.mp hleft with hs | hy
            · exact (ne_of_gt s3_pos (by nlinarith [hs] : s3 = 0)).elim
            · linarith
          · nlinarith [sq_nonneg y]
        have hx : x = -s3 := by
          simp [seamLminus, hy] at hL
          nlinarith [s3_sq]
        exact Or.inr (Or.inr (Or.inl ⟨hx, hy⟩))

/-- Exact algebraic reduction of failure of the first displayed seam corner:
all eleven possible vanishing factors land in the same six-point set. -/
theorem firstSeam_witness_zero_cases {x y : ℝ}
    (hzero : leadingFiniteCornerWitnessProduct
      (firstSeamChart standardOmega (seamCayley x) (seamCayley y)) = 0) :
    FirstSeamExceptional x y := by
  have hxnorm := seamCayley_normSq x
  have hynorm := seamCayley_normSq y
  simp only [leadingFiniteCornerWitnessProduct, mul_eq_zero] at hzero
  rcases hzero with hE | hB | hC | hB0 | hB3 | hBs0 | hBs3 |
      hC0 | hC3 | hCs0 | hCs3
  · exact firstSeam_detE_zero_cases hE
  · exact firstSeam_detB_zero_cases hB
  · exact firstSeam_detC_zero_cases hC
  · have hid := firstSeam_B0_formula hxnorm hynorm
    have hp3 : 3 * seamP_B0 (seamCayley x) (seamCayley y) = 0 := by
      simpa [hB0] using hid.symm
    have hp : seamP_B0 (seamCayley x) (seamCayley y) = 0 :=
      (mul_eq_zero.mp hp3).resolve_left (by norm_num)
    exact seamP_B0_zero_cases hp
  · have hid := firstSeam_B3_formula hxnorm hynorm
    have hp : seamP_B3 (seamCayley x) (seamCayley y) = 0 := by
      simpa [hB3] using hid.symm
    exact seamP_B3_zero_cases hp
  · have hid := firstSeam_Bswap0_formula hxnorm hynorm
    have hp : seamP_Bswap0 (seamCayley x) (seamCayley y) = 0 := by
      simpa [hBs0] using hid.symm
    exact seamP_Bswap0_zero_cases hp
  · have hid := firstSeam_Bswap3_formula hxnorm hynorm
    have hp : seamP_B3 (seamCayley x) (seamCayley y) = 0 := by
      simpa [hBs3] using hid.symm
    exact seamP_B3_zero_cases hp
  · have hid := firstSeam_C0_formula hxnorm hynorm
    have hp : seamP_C0 (seamCayley x) (seamCayley y) = 0 := by
      simpa [hC0] using hid.symm
    exact seamP_C0_zero_cases hp
  · have hid := firstSeam_C3_formula hxnorm hynorm
    have hp : seamP_C3 (seamCayley x) (seamCayley y) = 0 := by
      simpa [hC3] using hid.symm
    exact seamP_C3_zero_cases hp
  · have hid := firstSeam_Cswap0_formula hxnorm hynorm
    have hp : seamP_Cswap0 (seamCayley x) (seamCayley y) = 0 := by
      simpa [hCs0] using hid.symm
    exact seamP_Cswap0_zero_cases hp
  · have hid := firstSeam_Cswap3_formula hxnorm hynorm
    have hp : seamP_C3 (seamCayley x) (seamCayley y) = 0 := by
      simpa [hCs3] using hid.symm
    exact seamP_C3_zero_cases hp

/-- Normalize one concrete seam corner exactly and close each of the eleven
paper witness factors using only the cubic relation for `standardOmega`.
The six named lemmas below are the certificate table; this tactic contains
their shared arithmetic, not an additional mathematical assumption. -/
macro "close_standard_seam_corner" h:term : tactic => `(tactic| exact (by
  have hzero := $h
  have homega := standardOmega_isPrimitiveCubicPhase
  have hstar : star standardOmega = standardOmega ^ 2 :=
    primitiveCubicPhase_star homega
  have hstarSq : star (standardOmega ^ 2) = standardOmega := by
    rw [star_pow, hstar]
    calc
      (standardOmega ^ 2) ^ 2 = standardOmega * standardOmega ^ 3 := by ring
      _ = standardOmega := by rw [primitiveCubicPhase_cube homega, mul_one]
  have hcube := primitiveCubicPhase_cube homega
  have hpow4 : standardOmega ^ 4 = standardOmega := by
    calc
      standardOmega ^ 4 = standardOmega * standardOmega ^ 3 := by ring
      _ = standardOmega := by rw [hcube, mul_one]
  have hperiod (n : ℕ) : standardOmega ^ (n + 3) = standardOmega ^ n := by
    rw [pow_add, hcube, mul_one]
  have hp5 : standardOmega ^ 5 = standardOmega ^ 2 := by
    simpa using hperiod 2
  have hp6 : standardOmega ^ 6 = 1 := by simpa [hcube] using hperiod 3
  have hp7 : standardOmega ^ 7 = standardOmega := by
    simpa [hpow4] using hperiod 4
  have hp8 : standardOmega ^ 8 = standardOmega ^ 2 := by
    simpa [hp5] using hperiod 5
  have hp9 : standardOmega ^ 9 = 1 := by simpa [hp6] using hperiod 6
  have hp10 : standardOmega ^ 10 = standardOmega := by
    simpa [hp7] using hperiod 7
  have hp11 : standardOmega ^ 11 = standardOmega ^ 2 := by
    simpa [hp8] using hperiod 8
  have hp12 : standardOmega ^ 12 = 1 := by simpa [hp9] using hperiod 9
  have hp13 : standardOmega ^ 13 = standardOmega := by
    simpa [hp10] using hperiod 10
  have hp14 : standardOmega ^ 14 = standardOmega ^ 2 := by
    simpa [hp11] using hperiod 11
  have hp15 : standardOmega ^ 15 = 1 := by simpa [hp12] using hperiod 12
  have hp16 : standardOmega ^ 16 = standardOmega := by
    simpa [hp13] using hperiod 13
  have hp17 : standardOmega ^ 17 = standardOmega ^ 2 := by
    simpa [hp14] using hperiod 14
  have hp18 : standardOmega ^ 18 = 1 := by simpa [hp15] using hperiod 15
  have hsum : 1 + standardOmega + standardOmega ^ 2 = 0 := by
    linear_combination homega.2
  have hsq : standardOmega ^ 2 = -1 - standardOmega := by
    linear_combination hsum
  have hstarEnd :
      (starRingEnd ℂ) standardOmega = standardOmega ^ 2 := hstar
  simp only [leadingFiniteCornerWitnessProduct, mul_eq_zero] at hzero
  rcases hzero with h | h | h | h | h | h | h | h | h | h | h
  all_goals
    norm_num [affineFourierMatrix, dephase, dephaseRowFactor,
      dephaseColumnFactor, phaseTransform, reindexMatrix, seamRows012,
      seamColumns025,
      seamRows013_order.1, seamRows013_order.2.1,
      seamRows013_order.2.2.1, seamRows013_order.2.2.2.1,
      seamRows013_order.2.2.2.2.1, seamRows013_order.2.2.2.2.2,
      seamRows025_order.1, seamRows025_order.2.1,
      seamRows025_order.2.2.1, seamRows025_order.2.2.2.1,
      seamRows025_order.2.2.2.2.1, seamRows025_order.2.2.2.2.2,
      seamColumns024_order.1, seamColumns024_order.2.1,
      seamColumns024_order.2.2.1, seamColumns024_order.2.2.2.1,
      seamColumns024_order.2.2.2.2.1, seamColumns024_order.2.2.2.2.2,
      rowEndpoint0, rowEndpoint3, rowFibreEndpoint0, rowFibreEndpoint3,
      swapNoninitialRows, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁, seamCayley, hstar, hstarSq, hcube, hsum,
      Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] at h
    try simp_rw [hstarEnd] at h
    try simp only [hpow4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12,
      hp13, hp14, hp15, hp16, hp17, hp18, hsq] at h
    try ring_nf at h
    try simp only [hcube, hpow4, hp5, hp6, hp7, hp8, hp9, hp10, hp11,
      hp12, hp13, hp14, hp15, hp16, hp17, hp18, hsq] at h
    try ring_nf at h
    try simp only [hcube, hpow4, hp5, hp6, hp7, hp8, hp9, hp10, hp11,
      hp12, hp13, hp14, hp15, hp16, hp17, hp18, hsq] at h
    first
      | (rcases h with h | h <;>
          first
            | have him := congrArg Complex.im h
              (simp [standardOmega, Complex.mul_re, Complex.mul_im,
                Complex.conj_re, Complex.conj_im] at him <;>
                nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)])
            | norm_num at h)
      | have him := congrArg Complex.im h
        (simp [standardOmega, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im] at him <;>
          nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)])
      | norm_num at h))

/-! The six rows of the exceptional-point certificate table. -/

set_option maxHeartbeats 1000000 in
-- The exact exceptional-corner normalization needs the enlarged budget.
set_option maxRecDepth 100000 in

end

end Hadamard6
