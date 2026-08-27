import Hadamard6.FourierCubicAssembly
import Hadamard6.Classification
import Hadamard6.ConcreteClassification
import Hadamard6.SimultaneousFourierNormalization

/-!
# Classification of the simultaneous-Fourier branch

This module keeps the explicit normal form through the mixed factor cases
and proves the finite cubic branch internally.
-/

namespace Hadamard6

noncomputable section

private theorem normalization_mixed_case_classified
    {H : Mat6} (n : FourierNormalization H)
    (hp : IsCubicRoot n.p) (hq : IsCubicRoot n.q)
    (hr : IsCubicRoot n.r) (hs : IsCubicRoot n.s) :
    IsTaoOrbit H ∨ IsKarlssonConcrete H := by
  have hnormal : IsHadamard
      (fourierNormalForm n.ω n.p n.q n.r n.s
        (fourierForcedD n.ω n.p n.q n.r n.s)) := by
    rw [← n.normalForm]
    exact n.hK
  rcases cubicFourierNormalForm_classified
      (show IsPrimitiveCubicPhase n.ω from
        ⟨n.omega_unit, n.omega_quadratic⟩)
      hp hq hr hs hnormal with hTao | htwo
  · exact Or.inl (isTaoOrbit_of_equivalent n.equivalent (by
      rw [n.normalForm]
      exact hTao))
  · exact Or.inr ⟨
      (equivalent_isHadamard_iff n.equivalent).2 n.hK,
      hasHadamardTwoByTwo_of_equivalent n.equivalent (by
        rw [n.normalForm]
        exact htwo)⟩

/-- All four Hadamard blocks are classified internally from simultaneous
Fourier normalization: either the matrix is in Tao's orbit or it contains a
Hadamard `2 x 2` submatrix. -/
theorem allFourBlocks_classified
    (hnorm : FourierNormalizationReduction) :
    ∀ H, IsHadamard H → AllFourBlocksHadamard H →
      IsTaoOrbit H ∨ IsKarlssonConcrete H := by
  intro H hH hfour
  rcases hnorm H hH hfour with ⟨n⟩
  let ch := n.toCore
  rcases mul_eq_zero.mp ch.factor₁ with hα₁ | hA₁
  · rcases mul_eq_zero.mp ch.factor₂ with hα₂ | hA₂
    · exact Or.inr ⟨hH,
        hasHadamardTwoByTwo_of_equivalent n.equivalent
          (ch.K_twoByTwo_of_α_zero hα₁ hα₂)⟩
    · rcases A₂_zero_parameters_cubic ch.ω_unit ch.ω_cubic
          ch.p_unit ch.q_unit ch.A₂_formula hA₂ with ⟨hp, hq⟩
      rcases α₁_zero_parameters_cubic ch.ω_unit ch.ω_cubic
          ch.r_unit ch.s_unit ch.α₁_formula hα₁ with ⟨hr, hs⟩
      exact normalization_mixed_case_classified n hp hq hr hs
  · rcases mul_eq_zero.mp ch.factor₂ with hα₂ | hA₂
    · rcases A₁_zero_parameters_cubic ch.ω_unit ch.ω_cubic
          ch.p_unit ch.q_unit ch.A₁_formula hA₁ with ⟨hp, hq⟩
      rcases α₂_zero_parameters_cubic ch.ω_unit ch.ω_cubic
          ch.r_unit ch.s_unit ch.α₂_formula hα₂ with ⟨hr, hs⟩
      exact normalization_mixed_case_classified n hp hq hr hs
    · exact Or.inr ⟨hH,
        hasHadamardTwoByTwo_of_equivalent n.equivalent
          (ch.K_twoByTwo_of_A_zero hA₁ hA₂)⟩

/-- Every Hadamard matrix either belongs to the intrinsic Karlsson or Tao
sector, or is recovered from a finite corner. -/
theorem exceptional_or_finiteCornerAtlas :
    ∀ H : Mat6, IsHadamard H →
      InKnownExceptionalSector IsTaoOrbit IsKarlssonConcrete H ∨
        InFiniteCornerAtlas H := by
  apply exceptional_or_finiteCornerAtlas_of_routing
    IsTaoOrbit IsKarlssonConcrete
    (blockSwap_from_twoByTwo_input (by
      intro H hH htwo
      exact ⟨hH, htwo⟩))
  intro H hH hfour
  rcases allFourBlocks_classified
      (fourierNormalizationReduction_of_threeBlocks
        simultaneous_threeBlockFourierNormalization)
      H hH hfour with hTao | hKarlsson
  · exact Or.inr hTao
  · exact Or.inl hKarlsson

end

end Hadamard6
