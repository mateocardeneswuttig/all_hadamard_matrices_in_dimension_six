import Hadamard6.FourierSeamCertificate
import Hadamard6.IntrinsicKarlssonSeam
import Hadamard6.KarlssonGlobalModel
import Hadamard6.KarlssonParametrizationStatement

/-!
# Full Karlsson containment in the intrinsic finite-dilation output

This module mirrors the two-chart proof in the paper.  The regular chart is
closed internally by `KarlssonMixedBlocks.lean`.  The affine-Fourier seam is
closed internally by the kernel certificate in `FourierSeamCertificate.lean`.
The reciprocal half-angle equivalence, singly degenerate Möbius curves, and
the residual affine-Fourier seams are also checked internally.
-/

namespace Hadamard6

private theorem normSq_one_div_of_normSq_eq_one
    {z : ℂ} (hz : Complex.normSq z = 1) :
    Complex.normSq (1 / z) = 1 := by
  rw [one_div_eq_star_of_normSq_eq_one hz]
  simpa [Complex.star_def] using hz

/-- The new part of the Karlsson coverage proof.  Starting only from a raw
published parameter tuple, Lean chooses one of the two reciprocal half-angle
orientations, proves that the paper's fixed corner is regular there, and
transports its finite-corner witness back to the original matrix. -/
theorem canonicalKarlssonRawPresentation_mem_finiteCornerAtlas
    {H : Mat6} (hH : IsHadamard H)
    (q : CanonicalKarlssonRawPresentation H) : InFiniteCornerAtlas H := by
  rcases karlssonMPlus_ne_zero_in_one_orientation q.t_pos q.p_ne_neg_one
      q.not_common_fourier with hplus | hplusReciprocal
  · let K := karlssonMixedChartMatrix q.t q.p q.z₁ q.z₂ q.z₃ q.z₄
    have hrawMixed :
        Equivalent
          (karlssonRawMatrix q.t q.p q.z₁ q.z₂ q.z₃ q.z₄) K :=
      equivalent_karlssonMixedChartMatrix
        q.t q.p q.z₁ q.z₂ q.z₃ q.z₄
    have hHK : Equivalent H K :=
      equivalent_trans q.equivalent_raw hrawMixed
    have hK : IsHadamard K := (equivalent_isHadamard_iff hHK).1 hH
    have hregular : IsRegularKarlssonBlockPresentation K :=
      karlssonMixedChart_isRegular q.t_pos q.p_unit q.p_im_nonneg
        q.p_ne_neg_one hplus q.z₁_unit q.z₂_unit q.z₃_unit q.z₄_unit
    exact inFiniteCornerAtlas_of_equivalent hHK
      (regularKarlssonPresentation_mem_finiteCornerAtlas hK hregular)
  · have ht0 : q.t ≠ 0 := ne_of_gt q.t_pos
    have htReciprocal : 0 < 1 / q.t := one_div_pos.mpr q.t_pos
    have hz₁Reciprocal : Complex.normSq (-q.z₂) = 1 := by
      simpa [Complex.normSq_neg] using q.z₂_unit
    have hz₂Reciprocal : Complex.normSq (-q.z₁) = 1 := by
      simpa [Complex.normSq_neg] using q.z₁_unit
    have hz₃Reciprocal : Complex.normSq (1 / q.z₃) = 1 :=
      normSq_one_div_of_normSq_eq_one q.z₃_unit
    have hz₄Reciprocal : Complex.normSq (1 / q.z₄) = 1 :=
      normSq_one_div_of_normSq_eq_one q.z₄_unit
    let K := karlssonMixedChartMatrix (1 / q.t) q.p
      (-q.z₂) (-q.z₁) (1 / q.z₃) (1 / q.z₄)
    have hrawReciprocal :
        Equivalent (karlssonRawMatrix q.t q.p q.z₁ q.z₂ q.z₃ q.z₄)
          (karlssonRawMatrix (1 / q.t) q.p
            (-q.z₂) (-q.z₁) (1 / q.z₃) (1 / q.z₄)) :=
      equivalent_karlssonRawMatrix_reciprocal ht0 q.z₃_unit q.z₄_unit
    have hrawMixed :
        Equivalent
          (karlssonRawMatrix (1 / q.t) q.p
            (-q.z₂) (-q.z₁) (1 / q.z₃) (1 / q.z₄)) K :=
      equivalent_karlssonMixedChartMatrix (1 / q.t) q.p
        (-q.z₂) (-q.z₁) (1 / q.z₃) (1 / q.z₄)
    have hHK : Equivalent H K :=
      equivalent_trans q.equivalent_raw
        (equivalent_trans hrawReciprocal hrawMixed)
    have hK : IsHadamard K := (equivalent_isHadamard_iff hHK).1 hH
    have hregular : IsRegularKarlssonBlockPresentation K :=
      karlssonMixedChart_isRegular htReciprocal q.p_unit q.p_im_nonneg
        q.p_ne_neg_one hplusReciprocal hz₁Reciprocal hz₂Reciprocal
        hz₃Reciprocal hz₄Reciprocal
    exact inFiniteCornerAtlas_of_equivalent hHK
      (regularKarlssonPresentation_mem_finiteCornerAtlas hK hregular)

/-- Full intrinsic Karlsson containment, assembled in the same regular/seam
case split as the paper. -/
theorem hasHadamardTwoByTwo_mem_finiteCornerAtlas
    {H : Mat6} (hH : IsHadamard H)
    (hH₂ : HasHadamardTwoByTwo H) : InFiniteCornerAtlas H := by
  rcases karlssonRawOrSeamCoverage_proved H hH hH₂ with hraw | hseam
  · rcases hraw with ⟨q⟩
    exact canonicalKarlssonRawPresentation_mem_finiteCornerAtlas hH q
  · exact affineFourierSeam_mem_finiteCornerAtlas_proved hseam

end Hadamard6
