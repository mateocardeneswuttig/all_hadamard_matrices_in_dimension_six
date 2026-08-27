import Hadamard6.BlockGram
import Hadamard6.BlockCompletion
import Hadamard6.Strata

/-!
# Recovering a finite corner from a dephased block presentation
-/

namespace Hadamard6

theorem toBlocks₁₂_sixI :
    Matrix.toBlocks₁₂ ((6 : ℂ) • (1 : Mat6)) = 0 := by
  ext i j
  simp [Matrix.toBlocks₁₂]

theorem hadamard_top_row_cross {H : Mat6} (hH : IsHadamard H) :
    let E := Matrix.toBlocks₁₁ H
    let B := Matrix.toBlocks₁₂ H
    let C := Matrix.toBlocks₂₁ H
    let D := Matrix.toBlocks₂₂ H
    E * Matrix.conjTranspose C + B * Matrix.conjTranspose D = 0 := by
  have hg := hH.2
  rw [← Matrix.fromBlocks_toBlocks H, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply] at hg
  have h12 := congrArg Matrix.toBlocks₁₂ hg
  rw [toBlocks₁₂_sixI] at h12
  simpa using h12

theorem eq_forcedD_of_row_cross {E B C D : Mat3}
    (hB : IsUnit B.det)
    (hcross : E * Matrix.conjTranspose C +
      B * Matrix.conjTranspose D = 0) :
    D = forcedD E B C := by
  have hBD : B * Matrix.conjTranspose D =
      -(E * Matrix.conjTranspose C) := by
    exact eq_neg_of_add_eq_zero_right hcross
  have hstar : Matrix.conjTranspose D =
      -(B⁻¹ * E * Matrix.conjTranspose C) := by
    calc
      Matrix.conjTranspose D =
          B⁻¹ * (B * Matrix.conjTranspose D) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, one_mul]
      _ = B⁻¹ * (-(E * Matrix.conjTranspose C)) := by rw [hBD]
      _ = -(B⁻¹ * E * Matrix.conjTranspose C) := by
        simp [Matrix.mul_assoc]
  rw [← forcedD_conjTranspose E B C] at hstar
  have h := congrArg Matrix.conjTranspose hstar
  simpa using h

theorem topLeft_cornerData {H : Mat6}
    (hH : IsHadamard H) (hdeph : IsDephased H) :
    ∃ p : CornerData, p.matrix = Matrix.toBlocks₁₁ H := by
  let E := Matrix.toBlocks₁₁ H
  let p : CornerData :=
    { a := E 1 1
      b := E 1 2
      c := E 2 1
      d := E 2 2
      abs_a := hH.1 _ _
      abs_b := hH.1 _ _
      abs_c := hH.1 _ _
      abs_d := hH.1 _ _ }
  refine ⟨p, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [p, CornerData.matrix, corner, E, Matrix.toBlocks₁₁,
    hdeph.1, hdeph.2]

theorem topRight_mem_horizontalCandidates {H : Mat6}
    (hH : IsHadamard H) (hdeph : IsDephased H) :
    Matrix.toBlocks₁₂ H ∈
      horizontalCandidates (Matrix.toBlocks₁₁ H) := by
  refine ⟨(hadamard_blocks_entrywiseUnit hH).2.1, ?_,
    (hadamard_row_block_grams hH).1⟩
  intro j
  exact hdeph.1 _

theorem bottomLeft_mem_verticalCandidates {H : Mat6}
    (hH : IsHadamard H) (hdeph : IsDephased H) :
    Matrix.toBlocks₂₁ H ∈
      verticalCandidates (Matrix.toBlocks₁₁ H) := by
  refine ⟨(hadamard_blocks_entrywiseUnit hH).2.2.1, ?_,
    (hadamard_column_block_grams hH).1⟩
  intro i
  exact hdeph.2 _

theorem finite_topLeft_fibres_give_finiteCorner
    {H : Mat6} (hH : IsHadamard H) (hdeph : IsDephased H)
    (_hdetE : (Matrix.toBlocks₁₁ H).det ≠ 0)
    (hdetB : (Matrix.toBlocks₁₂ H).det ≠ 0)
    (hdetC : (Matrix.toBlocks₂₁ H).det ≠ 0)
    (hfinB : (horizontalCandidates (Matrix.toBlocks₁₁ H)).Finite)
    (hfinC : (verticalCandidates (Matrix.toBlocks₁₁ H)).Finite) :
    HasFiniteCorner H := by
  let E := Matrix.toBlocks₁₁ H
  let B := Matrix.toBlocks₁₂ H
  let C := Matrix.toBlocks₂₁ H
  let D := Matrix.toBlocks₂₂ H
  have hBu : IsUnit B.det := by simpa [isUnit_iff_ne_zero] using hdetB
  have hCu : IsUnit C.det := by simpa [isUnit_iff_ne_zero] using hdetC
  have hBmem : B ∈ horizontalCandidates E :=
    topRight_mem_horizontalCandidates hH hdeph
  have hCmem : C ∈ verticalCandidates E :=
    bottomLeft_mem_verticalCandidates hH hdeph
  have hfinite : IsFiniteDilationCorner E := by
    refine ⟨⟨B, hBmem, hBu⟩, ⟨C, hCmem, hCu⟩, ?_, ?_⟩
    · exact hfinB.subset (fun _ h ↦ h.1)
    · exact hfinC.subset (fun _ h ↦ h.1)
  rcases topLeft_cornerData hH hdeph with ⟨p, hp⟩
  have hDforced : D = forcedD E B C :=
    eq_forcedD_of_row_cross hBu (hadamard_top_row_cross hH)
  refine ⟨p, B, C, D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hp] using hfinite
  · simpa [hp] using show B ∈ invertibleHorizontalCandidates E from
      ⟨hBmem, hBu⟩
  · simpa [hp] using show C ∈ invertibleVerticalCandidates E from
      ⟨hCmem, hCu⟩
  · exact (hadamard_blocks_entrywiseUnit hH).2.2.2
  · simpa [hp] using hDforced
  · have hblocks : Matrix.fromBlocks E B C D = H :=
      Matrix.fromBlocks_toBlocks H
    rw [hp]
    change Equivalent H (Matrix.fromBlocks E B C D)
    rw [hblocks]
    exact equivalent_refl H

end Hadamard6
