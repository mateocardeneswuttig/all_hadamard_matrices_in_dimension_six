import Hadamard6.FourierCubicClassification

namespace Hadamard6

noncomputable section

set_option maxHeartbeats 3000000 in
theorem cubicTaoCase0_dephased_eq
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega) :
    CubicTaoCertificate omega 0 := by
  rcases cubicPowerFacts homega with ⟨h3, h4, h5, h6, h7, h8⟩
  have hstar : (starRingEnd ℂ) omega = omega ^ 2 :=
    primitiveCubicPhase_star homega
  have h9 : omega ^ 9 = 1 := by
    rw [show omega ^ 9 = (omega ^ 3) ^ 3 by ring, h3]
    norm_num
  have h10 : omega ^ 10 = omega := by
    rw [show omega ^ 10 = omega * omega ^ 9 by ring, h9, mul_one]
  have h11 : omega ^ 11 = omega ^ 2 := by
    rw [show omega ^ 11 = omega ^ 2 * omega ^ 9 by ring, h9, mul_one]
  have h12 : omega ^ 12 = 1 := by
    rw [show omega ^ 12 = (omega ^ 3) ^ 4 by ring, h3]
    norm_num
  have h13 : omega ^ 13 = omega := by
    rw [show omega ^ 13 = omega * omega ^ 12 by ring, h12, mul_one]
  have h14 : omega ^ 14 = omega ^ 2 := by
    rw [show omega ^ 14 = omega ^ 2 * omega ^ 12 by ring, h12, mul_one]
  have h15 : omega ^ 15 = 1 := by
    rw [show omega ^ 15 = (omega ^ 3) ^ 5 by ring, h3]
    norm_num
  have h16 : omega ^ 16 = omega := by
    rw [show omega ^ 16 = omega * omega ^ 15 by ring, h15, mul_one]
  have h17 : omega ^ 17 = omega ^ 2 := by
    rw [show omega ^ 17 = omega ^ 2 * omega ^ 15 by ring, h15, mul_one]
  have h18 : omega ^ 18 = 1 := by
    rw [show omega ^ 18 = (omega ^ 3) ^ 6 by ring, h3]
    norm_num
  have h19 : omega ^ 19 = omega := by
    rw [show omega ^ 19 = omega * omega ^ 18 by ring, h18, mul_one]
  have h20 : omega ^ 20 = omega ^ 2 := by
    rw [show omega ^ 20 = omega ^ 2 * omega ^ 18 by ring, h18, mul_one]
  unfold CubicTaoCertificate
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [cubicTaoP, cubicTaoQ, cubicTaoR, cubicTaoS,
      cubicTaoTarget, cubicTaoPermutation,
      cubicIndex0, cubicIndex1, cubicIndex2, cubicIndex3,
      cubicIndex4, cubicIndex5, reindexMatrix, dephase,
      phaseTransform, dephaseRowFactor, dephaseColumnFactor,
      fourierNormalForm, fourier3, rowGauge, columnGauge,
      fourierParameters, fourierForcedD, dftEntry₀, dftEntry₁,
      dftEntry₂, zCol₀, zCol₁, zCol₂, vHat₀, vHat₁, vHat₂,
      dft₀, dft₁, dft₂, taoMatrix]
  all_goals try simp only [hstar]
  all_goals try ring_nf
  all_goals try simp [h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
  all_goals try ring_nf
  all_goals try linear_combination (-4 / 3 : ℂ) * homega.2

set_option maxHeartbeats 3000000 in
theorem cubicTaoCase1_dephased_eq
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega) :
    CubicTaoCertificate omega 1 := by
  rcases cubicPowerFacts homega with ⟨h3, h4, h5, h6, h7, h8⟩
  have hstar : (starRingEnd ℂ) omega = omega ^ 2 :=
    primitiveCubicPhase_star homega
  have h9 : omega ^ 9 = 1 := by
    rw [show omega ^ 9 = (omega ^ 3) ^ 3 by ring, h3]
    norm_num
  have h10 : omega ^ 10 = omega := by
    rw [show omega ^ 10 = omega * omega ^ 9 by ring, h9, mul_one]
  have h11 : omega ^ 11 = omega ^ 2 := by
    rw [show omega ^ 11 = omega ^ 2 * omega ^ 9 by ring, h9, mul_one]
  have h12 : omega ^ 12 = 1 := by
    rw [show omega ^ 12 = (omega ^ 3) ^ 4 by ring, h3]
    norm_num
  have h13 : omega ^ 13 = omega := by
    rw [show omega ^ 13 = omega * omega ^ 12 by ring, h12, mul_one]
  have h14 : omega ^ 14 = omega ^ 2 := by
    rw [show omega ^ 14 = omega ^ 2 * omega ^ 12 by ring, h12, mul_one]
  have h15 : omega ^ 15 = 1 := by
    rw [show omega ^ 15 = (omega ^ 3) ^ 5 by ring, h3]
    norm_num
  have h16 : omega ^ 16 = omega := by
    rw [show omega ^ 16 = omega * omega ^ 15 by ring, h15, mul_one]
  have h17 : omega ^ 17 = omega ^ 2 := by
    rw [show omega ^ 17 = omega ^ 2 * omega ^ 15 by ring, h15, mul_one]
  have h18 : omega ^ 18 = 1 := by
    rw [show omega ^ 18 = (omega ^ 3) ^ 6 by ring, h3]
    norm_num
  have h19 : omega ^ 19 = omega := by
    rw [show omega ^ 19 = omega * omega ^ 18 by ring, h18, mul_one]
  have h20 : omega ^ 20 = omega ^ 2 := by
    rw [show omega ^ 20 = omega ^ 2 * omega ^ 18 by ring, h18, mul_one]
  unfold CubicTaoCertificate
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [cubicTaoP, cubicTaoQ, cubicTaoR, cubicTaoS,
      cubicTaoTarget, cubicTaoPermutation,
      cubicIndex0, cubicIndex1, cubicIndex2, cubicIndex3,
      cubicIndex4, cubicIndex5, reindexMatrix, dephase,
      phaseTransform, dephaseRowFactor, dephaseColumnFactor,
      fourierNormalForm, fourier3, rowGauge, columnGauge,
      fourierParameters, fourierForcedD, dftEntry₀, dftEntry₁,
      dftEntry₂, zCol₀, zCol₁, zCol₂, vHat₀, vHat₁, vHat₂,
      dft₀, dft₁, dft₂, taoMatrix]
  all_goals try simp only [hstar]
  all_goals try ring_nf
  all_goals try simp [h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
  all_goals try ring_nf
  all_goals try linear_combination (-4 / 3 : ℂ) * homega.2

set_option maxHeartbeats 3000000 in
theorem cubicTaoCase2_dephased_eq
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega) :
    CubicTaoCertificate omega 2 := by
  rcases cubicPowerFacts homega with ⟨h3, h4, h5, h6, h7, h8⟩
  have hstar : (starRingEnd ℂ) omega = omega ^ 2 :=
    primitiveCubicPhase_star homega
  have h9 : omega ^ 9 = 1 := by
    rw [show omega ^ 9 = (omega ^ 3) ^ 3 by ring, h3]
    norm_num
  have h10 : omega ^ 10 = omega := by
    rw [show omega ^ 10 = omega * omega ^ 9 by ring, h9, mul_one]
  have h11 : omega ^ 11 = omega ^ 2 := by
    rw [show omega ^ 11 = omega ^ 2 * omega ^ 9 by ring, h9, mul_one]
  have h12 : omega ^ 12 = 1 := by
    rw [show omega ^ 12 = (omega ^ 3) ^ 4 by ring, h3]
    norm_num
  have h13 : omega ^ 13 = omega := by
    rw [show omega ^ 13 = omega * omega ^ 12 by ring, h12, mul_one]
  have h14 : omega ^ 14 = omega ^ 2 := by
    rw [show omega ^ 14 = omega ^ 2 * omega ^ 12 by ring, h12, mul_one]
  have h15 : omega ^ 15 = 1 := by
    rw [show omega ^ 15 = (omega ^ 3) ^ 5 by ring, h3]
    norm_num
  have h16 : omega ^ 16 = omega := by
    rw [show omega ^ 16 = omega * omega ^ 15 by ring, h15, mul_one]
  have h17 : omega ^ 17 = omega ^ 2 := by
    rw [show omega ^ 17 = omega ^ 2 * omega ^ 15 by ring, h15, mul_one]
  have h18 : omega ^ 18 = 1 := by
    rw [show omega ^ 18 = (omega ^ 3) ^ 6 by ring, h3]
    norm_num
  have h19 : omega ^ 19 = omega := by
    rw [show omega ^ 19 = omega * omega ^ 18 by ring, h18, mul_one]
  have h20 : omega ^ 20 = omega ^ 2 := by
    rw [show omega ^ 20 = omega ^ 2 * omega ^ 18 by ring, h18, mul_one]
  unfold CubicTaoCertificate
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [cubicTaoP, cubicTaoQ, cubicTaoR, cubicTaoS,
      cubicTaoTarget, cubicTaoPermutation,
      cubicIndex0, cubicIndex1, cubicIndex2, cubicIndex3,
      cubicIndex4, cubicIndex5, reindexMatrix, dephase,
      phaseTransform, dephaseRowFactor, dephaseColumnFactor,
      fourierNormalForm, fourier3, rowGauge, columnGauge,
      fourierParameters, fourierForcedD, dftEntry₀, dftEntry₁,
      dftEntry₂, zCol₀, zCol₁, zCol₂, vHat₀, vHat₁, vHat₂,
      dft₀, dft₁, dft₂, taoMatrix]
  all_goals try simp only [hstar]
  all_goals try ring_nf
  all_goals try simp [h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
  all_goals try ring_nf
  all_goals try linear_combination (-4 / 3 : ℂ) * homega.2

set_option maxHeartbeats 3000000 in
theorem cubicTaoCase3_dephased_eq
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega) :
    CubicTaoCertificate omega 3 := by
  rcases cubicPowerFacts homega with ⟨h3, h4, h5, h6, h7, h8⟩
  have hstar : (starRingEnd ℂ) omega = omega ^ 2 :=
    primitiveCubicPhase_star homega
  have h9 : omega ^ 9 = 1 := by
    rw [show omega ^ 9 = (omega ^ 3) ^ 3 by ring, h3]
    norm_num
  have h10 : omega ^ 10 = omega := by
    rw [show omega ^ 10 = omega * omega ^ 9 by ring, h9, mul_one]
  have h11 : omega ^ 11 = omega ^ 2 := by
    rw [show omega ^ 11 = omega ^ 2 * omega ^ 9 by ring, h9, mul_one]
  have h12 : omega ^ 12 = 1 := by
    rw [show omega ^ 12 = (omega ^ 3) ^ 4 by ring, h3]
    norm_num
  have h13 : omega ^ 13 = omega := by
    rw [show omega ^ 13 = omega * omega ^ 12 by ring, h12, mul_one]
  have h14 : omega ^ 14 = omega ^ 2 := by
    rw [show omega ^ 14 = omega ^ 2 * omega ^ 12 by ring, h12, mul_one]
  have h15 : omega ^ 15 = 1 := by
    rw [show omega ^ 15 = (omega ^ 3) ^ 5 by ring, h3]
    norm_num
  have h16 : omega ^ 16 = omega := by
    rw [show omega ^ 16 = omega * omega ^ 15 by ring, h15, mul_one]
  have h17 : omega ^ 17 = omega ^ 2 := by
    rw [show omega ^ 17 = omega ^ 2 * omega ^ 15 by ring, h15, mul_one]
  have h18 : omega ^ 18 = 1 := by
    rw [show omega ^ 18 = (omega ^ 3) ^ 6 by ring, h3]
    norm_num
  have h19 : omega ^ 19 = omega := by
    rw [show omega ^ 19 = omega * omega ^ 18 by ring, h18, mul_one]
  have h20 : omega ^ 20 = omega ^ 2 := by
    rw [show omega ^ 20 = omega ^ 2 * omega ^ 18 by ring, h18, mul_one]
  unfold CubicTaoCertificate
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [cubicTaoP, cubicTaoQ, cubicTaoR, cubicTaoS,
      cubicTaoTarget, cubicTaoPermutation,
      cubicIndex0, cubicIndex1, cubicIndex2, cubicIndex3,
      cubicIndex4, cubicIndex5, reindexMatrix, dephase,
      phaseTransform, dephaseRowFactor, dephaseColumnFactor,
      fourierNormalForm, fourier3, rowGauge, columnGauge,
      fourierParameters, fourierForcedD, dftEntry₀, dftEntry₁,
      dftEntry₂, zCol₀, zCol₁, zCol₂, vHat₀, vHat₁, vHat₂,
      dft₀, dft₁, dft₂, taoMatrix]
  all_goals try simp only [hstar]
  all_goals try ring_nf
  all_goals try simp [h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
  all_goals try ring_nf
  all_goals try linear_combination (-4 / 3 : ℂ) * homega.2

set_option maxHeartbeats 3000000 in
theorem cubicTaoCase4_dephased_eq
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega) :
    CubicTaoCertificate omega 4 := by
  rcases cubicPowerFacts homega with ⟨h3, h4, h5, h6, h7, h8⟩
  have hstar : (starRingEnd ℂ) omega = omega ^ 2 :=
    primitiveCubicPhase_star homega
  have h9 : omega ^ 9 = 1 := by
    rw [show omega ^ 9 = (omega ^ 3) ^ 3 by ring, h3]
    norm_num
  have h10 : omega ^ 10 = omega := by
    rw [show omega ^ 10 = omega * omega ^ 9 by ring, h9, mul_one]
  have h11 : omega ^ 11 = omega ^ 2 := by
    rw [show omega ^ 11 = omega ^ 2 * omega ^ 9 by ring, h9, mul_one]
  have h12 : omega ^ 12 = 1 := by
    rw [show omega ^ 12 = (omega ^ 3) ^ 4 by ring, h3]
    norm_num
  have h13 : omega ^ 13 = omega := by
    rw [show omega ^ 13 = omega * omega ^ 12 by ring, h12, mul_one]
  have h14 : omega ^ 14 = omega ^ 2 := by
    rw [show omega ^ 14 = omega ^ 2 * omega ^ 12 by ring, h12, mul_one]
  have h15 : omega ^ 15 = 1 := by
    rw [show omega ^ 15 = (omega ^ 3) ^ 5 by ring, h3]
    norm_num
  have h16 : omega ^ 16 = omega := by
    rw [show omega ^ 16 = omega * omega ^ 15 by ring, h15, mul_one]
  have h17 : omega ^ 17 = omega ^ 2 := by
    rw [show omega ^ 17 = omega ^ 2 * omega ^ 15 by ring, h15, mul_one]
  have h18 : omega ^ 18 = 1 := by
    rw [show omega ^ 18 = (omega ^ 3) ^ 6 by ring, h3]
    norm_num
  have h19 : omega ^ 19 = omega := by
    rw [show omega ^ 19 = omega * omega ^ 18 by ring, h18, mul_one]
  have h20 : omega ^ 20 = omega ^ 2 := by
    rw [show omega ^ 20 = omega ^ 2 * omega ^ 18 by ring, h18, mul_one]
  unfold CubicTaoCertificate
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [cubicTaoP, cubicTaoQ, cubicTaoR, cubicTaoS,
      cubicTaoTarget, cubicTaoPermutation,
      cubicIndex0, cubicIndex1, cubicIndex2, cubicIndex3,
      cubicIndex4, cubicIndex5, reindexMatrix, dephase,
      phaseTransform, dephaseRowFactor, dephaseColumnFactor,
      fourierNormalForm, fourier3, rowGauge, columnGauge,
      fourierParameters, fourierForcedD, dftEntry₀, dftEntry₁,
      dftEntry₂, zCol₀, zCol₁, zCol₂, vHat₀, vHat₁, vHat₂,
      dft₀, dft₁, dft₂, taoMatrix]
  all_goals try simp only [hstar]
  all_goals try ring_nf
  all_goals try simp [h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
  all_goals try ring_nf
  all_goals try linear_combination (-4 / 3 : ℂ) * homega.2

set_option maxHeartbeats 3000000 in
theorem cubicTaoCase5_dephased_eq
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega) :
    CubicTaoCertificate omega 5 := by
  rcases cubicPowerFacts homega with ⟨h3, h4, h5, h6, h7, h8⟩
  have hstar : (starRingEnd ℂ) omega = omega ^ 2 :=
    primitiveCubicPhase_star homega
  have h9 : omega ^ 9 = 1 := by
    rw [show omega ^ 9 = (omega ^ 3) ^ 3 by ring, h3]
    norm_num
  have h10 : omega ^ 10 = omega := by
    rw [show omega ^ 10 = omega * omega ^ 9 by ring, h9, mul_one]
  have h11 : omega ^ 11 = omega ^ 2 := by
    rw [show omega ^ 11 = omega ^ 2 * omega ^ 9 by ring, h9, mul_one]
  have h12 : omega ^ 12 = 1 := by
    rw [show omega ^ 12 = (omega ^ 3) ^ 4 by ring, h3]
    norm_num
  have h13 : omega ^ 13 = omega := by
    rw [show omega ^ 13 = omega * omega ^ 12 by ring, h12, mul_one]
  have h14 : omega ^ 14 = omega ^ 2 := by
    rw [show omega ^ 14 = omega ^ 2 * omega ^ 12 by ring, h12, mul_one]
  have h15 : omega ^ 15 = 1 := by
    rw [show omega ^ 15 = (omega ^ 3) ^ 5 by ring, h3]
    norm_num
  have h16 : omega ^ 16 = omega := by
    rw [show omega ^ 16 = omega * omega ^ 15 by ring, h15, mul_one]
  have h17 : omega ^ 17 = omega ^ 2 := by
    rw [show omega ^ 17 = omega ^ 2 * omega ^ 15 by ring, h15, mul_one]
  have h18 : omega ^ 18 = 1 := by
    rw [show omega ^ 18 = (omega ^ 3) ^ 6 by ring, h3]
    norm_num
  have h19 : omega ^ 19 = omega := by
    rw [show omega ^ 19 = omega * omega ^ 18 by ring, h18, mul_one]
  have h20 : omega ^ 20 = omega ^ 2 := by
    rw [show omega ^ 20 = omega ^ 2 * omega ^ 18 by ring, h18, mul_one]
  unfold CubicTaoCertificate
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [cubicTaoP, cubicTaoQ, cubicTaoR, cubicTaoS,
      cubicTaoTarget, cubicTaoPermutation,
      cubicIndex0, cubicIndex1, cubicIndex2, cubicIndex3,
      cubicIndex4, cubicIndex5, reindexMatrix, dephase,
      phaseTransform, dephaseRowFactor, dephaseColumnFactor,
      fourierNormalForm, fourier3, rowGauge, columnGauge,
      fourierParameters, fourierForcedD, dftEntry₀, dftEntry₁,
      dftEntry₂, zCol₀, zCol₁, zCol₂, vHat₀, vHat₁, vHat₂,
      dft₀, dft₁, dft₂, taoMatrix]
  all_goals try simp only [hstar]
  all_goals try ring_nf
  all_goals try simp [h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
  all_goals try ring_nf
  all_goals try linear_combination (-4 / 3 : ℂ) * homega.2

end

end Hadamard6

