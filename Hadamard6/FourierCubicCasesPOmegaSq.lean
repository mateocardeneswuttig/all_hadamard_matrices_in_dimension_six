import Hadamard6.FourierCubicTaoTable

/-!
# Cubic simultaneous-Fourier cases with p = (omega ^ 2)
-/

namespace Hadamard6

noncomputable section

theorem cubicFourierNormalForm_classified_p_omega_sq
    {omega q r s : ℂ}
    (homega : IsPrimitiveCubicPhase omega)
    (hq : IsCubicRoot q) (hr : IsCubicRoot r) (hs : IsCubicRoot s)
    (hH : IsHadamard
      (fourierNormalForm omega (omega ^ 2) q r s
        (fourierForcedD omega (omega ^ 2) q r s))) :
    IsTaoOrbit
        (fourierNormalForm omega (omega ^ 2) q r s
          (fourierForcedD omega (omega ^ 2) q r s)) ∨
      HasHadamardTwoByTwo
        (fourierNormalForm omega (omega ^ 2) q r s
          (fourierForcedD omega (omega ^ 2) q r s)) := by
  rcases cubicPowerFacts homega with ⟨h3, h4, h5, h6, h7, h8⟩
  have hsq : (omega ^ 2) = -omega - 1 := by
    linear_combination homega.2
  have htwo (k : I3)
      (hk : fourierForcedD omega (omega ^ 2) q r s 0 k = -1) :
      IsTaoOrbit
          (fourierNormalForm omega (omega ^ 2) q r s
            (fourierForcedD omega (omega ^ 2) q r s)) ∨
        HasHadamardTwoByTwo
          (fourierNormalForm omega (omega ^ 2) q r s
            (fourierForcedD omega (omega ^ 2) q r s)) :=
    Or.inr (fourierNormalForm_hasTwoByTwo_of_D_entry_neg_one hk)
  have hzero (i j : I3)
      (hz : fourierForcedD omega (omega ^ 2) q r s i j = 0) :
      IsTaoOrbit
          (fourierNormalForm omega (omega ^ 2) q r s
            (fourierForcedD omega (omega ^ 2) q r s)) ∨
        HasHadamardTwoByTwo
          (fourierNormalForm omega (omega ^ 2) q r s
            (fourierForcedD omega (omega ^ 2) q r s)) :=
    (false_of_fourierForcedD_entry_zero hH hz).elim
  rcases cubicRoot_eq_one_or_primitive_or_sq homega hq with hq0 | hq1 | hq2 <;>
    subst q <;>
  rcases cubicRoot_eq_one_or_primitive_or_sq homega hr with hr0 | hr1 | hr2 <;>
    subst r <;>
  rcases cubicRoot_eq_one_or_primitive_or_sq homega hs with hs0 | hs1 | hs2 <;>
    subst s
  · apply htwo 0
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · exact Or.inl (by
      simpa [cubicTaoP, cubicTaoQ, cubicTaoR, cubicTaoS] using
        cubicTaoTable_isTaoOrbit homega (n := 12) hH)
  · apply hzero 1 0
    simp [fourierForcedD, dftEntry₁, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · exact Or.inl (by
      simpa [cubicTaoP, cubicTaoQ, cubicTaoR, cubicTaoS] using
        cubicTaoTable_isTaoOrbit homega (n := 13) hH)
  · apply hzero 0 1
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply htwo 1
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply hzero 0 1
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply htwo 0
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · exact Or.inl (by
      simpa [cubicTaoP, cubicTaoQ, cubicTaoR, cubicTaoS] using
        cubicTaoTable_isTaoOrbit homega (n := 14) hH)
  · apply htwo 0
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply htwo 1
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply htwo 1
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply htwo 0
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply htwo 1
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply htwo 1
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply htwo 0
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply htwo 1
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply htwo 1
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply htwo 0
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply hzero 2 1
    simp [fourierForcedD, dftEntry₂, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · exact Or.inl (by
      simpa [cubicTaoP, cubicTaoQ, cubicTaoR, cubicTaoS] using
        cubicTaoTable_isTaoOrbit homega (n := 15) hH)
  · apply hzero 1 1
    simp [fourierForcedD, dftEntry₁, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · exact Or.inl (by
      simpa [cubicTaoP, cubicTaoQ, cubicTaoR, cubicTaoS] using
        cubicTaoTable_isTaoOrbit homega (n := 16) hH)
  · apply htwo 1
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · exact Or.inl (by
      simpa [cubicTaoP, cubicTaoQ, cubicTaoR, cubicTaoS] using
        cubicTaoTable_isTaoOrbit homega (n := 17) hH)
  · apply htwo 2
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring
  · apply hzero 0 1
    simp [fourierForcedD, dftEntry₀, zCol₀, zCol₁, zCol₂,
      vHat₀, vHat₁, vHat₂, dft₀, dft₁, dft₂,
      h3, h4, h5, h6, h7, h8] <;> ring_nf <;>
      simp [h3, h4, h5, h6, h7, h8, hsq] <;> ring

end

end Hadamard6
