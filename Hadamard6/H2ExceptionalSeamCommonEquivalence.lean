import Hadamard6.H2ExceptionalSeamCommonAlgebra
import Hadamard6.H2RawPairSigns

/-!
# Exact affine-Fourier equivalences at the common point

The permutations below are the pair reorderings visible in the canonical
`2 × 2` block array.  The identities are checked entry by entry.
-/

namespace Hadamard6

noncomputable section

def commonRightPlusPlusPermutation : Equiv.Perm I6 :=
  Equiv.swap h2Tail₁ h2Tail₃

def commonRightPlusMinusPermutation : Equiv.Perm I6 :=
  (Equiv.swap h2Tail₁ h2Tail₂).trans
    (Equiv.swap h2Tail₁ h2Tail₃)

def commonRightMinusPlusPermutation : Equiv.Perm I6 :=
  (Equiv.swap h2Tail₀ h2Tail₁).trans
    (Equiv.swap h2Tail₀ h2Tail₃)

def commonRightMinusMinusPermutation : Equiv.Perm I6 :=
  ((Equiv.swap h2Tail₀ h2Tail₁).trans
    (Equiv.swap h2Tail₀ h2Tail₂)).trans
    (Equiv.swap h2Tail₀ h2Tail₃)

private theorem standardOmega_cube : standardOmega ^ 3 = 1 :=
  primitiveCubicPhase_cube standardOmega_isPrimitiveCubicPhase

private theorem standardOmega_fourth :
    (standardOmega ^ 2) ^ 2 = standardOmega := by
  calc
    (standardOmega ^ 2) ^ 2 =
        standardOmega * standardOmega ^ 3 := by ring
    _ = standardOmega := by rw [standardOmega_cube, mul_one]

private theorem standardOmega_pow_four : standardOmega ^ 4 = standardOmega := by
  calc
    standardOmega ^ 4 = standardOmega * standardOmega ^ 3 := by ring
    _ = standardOmega := by rw [standardOmega_cube, mul_one]

private theorem standardOmega_mul_sq :
    standardOmega * standardOmega ^ 2 = 1 := by
  calc
    standardOmega * standardOmega ^ 2 = standardOmega ^ 3 := by ring
    _ = 1 := standardOmega_cube

private theorem standardOmega_sq_mul :
    standardOmega ^ 2 * standardOmega = 1 := by
  rw [mul_comm]
  exact standardOmega_mul_sq

private theorem standardOmega_mul_self :
    standardOmega * standardOmega = standardOmega ^ 2 := by
  rw [pow_two]

private theorem standardOmega_sq_mul_sq :
    standardOmega ^ 2 * standardOmega ^ 2 = standardOmega := by
  simpa only [pow_two] using standardOmega_fourth

set_option maxHeartbeats 1000000 in
-- This is a finite check of all 36 entries of the displayed equivalence.
theorem common_right_plus_plus_eq_affine_transpose
    (z₃ z₄ : ℂ) :
    reindexMatrix (Equiv.refl I6) commonRightPlusPlusPermutation
        (karlssonRawMatrix 1 1 1 1 z₃ z₄) =
      (affineFourierMatrix standardOmega z₃ z₄).transpose := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [commonRightPlusPlusPermutation, karlssonRawMatrix, reindexMatrix,
      karlssonMixedChartMatrix, karlssonMixedE, karlssonMixedB,
      karlssonMixedC, karlssonMixedD, mixedLeadingBlock,
      mixedHorizontalBlock, affineFourierMatrix, karlssonBlockProduct,
      karlssonZLeft, karlssonZRight, karlssonCoreA_one_one,
      karlssonCoreB_one_one, h2Tail₀, h2Tail₁, h2Tail₂, h2Tail₃,
      Equiv.swap_apply_def, standardOmega_cube, standardOmega_fourth] <;>
    ring

def commonZ₁BranchPermutation : Equiv.Perm I6 :=
  karlssonMixedPermutation.symm

def commonZ₂BranchPermutation : Equiv.Perm I6 :=
  (Equiv.swap (Sum.inl 1) h2Tail₃).trans
    (Equiv.swap (Sum.inl 1) h2Tail₂)

set_option maxHeartbeats 1000000 in
-- This is a finite check of all 36 entries of the displayed equivalence.
theorem common_z₁_branch_eq_affine
    (z₂ : ℂ) :
    reindexMatrix (Equiv.refl I6) commonZ₁BranchPermutation
        (karlssonRawMatrix 1 1 1 z₂ standardOmega
          (standardOmega ^ 2)) =
      affineFourierMatrix standardOmega (-1) z₂ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [commonZ₁BranchPermutation, karlssonRawMatrix, reindexMatrix,
      karlssonMixedChartMatrix, karlssonMixedE, karlssonMixedB,
      karlssonMixedC, karlssonMixedD, mixedLeadingBlock,
      mixedHorizontalBlock, affineFourierMatrix, karlssonBlockProduct,
      karlssonZLeft, karlssonZRight, karlssonCoreA_one_one,
      karlssonCoreB_one_one]
  all_goals
    simp only [standardOmega_cube, standardOmega_pow_four,
      standardOmega_mul_sq, standardOmega_sq_mul,
      standardOmega_mul_self, standardOmega_sq_mul_sq]
    ring

set_option maxHeartbeats 1000000 in
-- This is a finite check of all 36 entries of the displayed equivalence.
theorem common_z₂_branch_eq_affine
    (z₁ : ℂ) :
    reindexMatrix (Equiv.refl I6) commonZ₂BranchPermutation
        (karlssonRawMatrix 1 1 z₁ 1 (standardOmega ^ 2)
          standardOmega) =
      affineFourierMatrix standardOmega z₁ (-1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [commonZ₂BranchPermutation, karlssonRawMatrix, reindexMatrix,
      karlssonMixedChartMatrix, karlssonMixedE, karlssonMixedB,
      karlssonMixedC, karlssonMixedD, mixedLeadingBlock,
      mixedHorizontalBlock, affineFourierMatrix, karlssonBlockProduct,
      karlssonZLeft, karlssonZRight, karlssonCoreA_one_one,
      karlssonCoreB_one_one, h2Tail₀, h2Tail₁, h2Tail₂, h2Tail₃,
      Equiv.swap_apply_def]
  all_goals
    simp only [standardOmega_cube, standardOmega_pow_four,
      standardOmega_mul_sq, standardOmega_sq_mul,
      standardOmega_mul_self, standardOmega_sq_mul_sq]
    ring

private theorem standardOmega_sq_ne_standardOmega :
    standardOmega ^ 2 ≠ standardOmega := by
  intro h
  have hω0 := primitiveCubicPhase_ne_zero
    standardOmega_isPrimitiveCubicPhase
  have hω1 : standardOmega = 1 := by
    apply (mul_left_cancel₀ hω0)
    simpa [pow_two] using h
  exact primitiveCubicPhase_ne_one standardOmega_isPrimitiveCubicPhase hω1

private theorem equivalent_normalize_z₁_sign
    {z₁ z₂ z₃ z₄ : ℂ} (hz₁ : z₁ ^ 2 = 1) :
    Equivalent (karlssonRawMatrix 1 1 z₁ z₂ z₃ z₄)
      (karlssonRawMatrix 1 1 1 z₂ z₃ z₄) := by
  rcases (sq_eq_one_iff).mp hz₁ with h | h
  · simpa [h] using equivalent_refl' (karlssonRawMatrix 1 1 1 z₂ z₃ z₄)
  · simpa [h] using
      equivalent_karlssonRawMatrix_neg_z₁ 1 1 (-1) z₂ z₃ z₄

private theorem equivalent_normalize_z₂_sign
    {z₁ z₂ z₃ z₄ : ℂ} (hz₂ : z₂ ^ 2 = 1) :
    Equivalent (karlssonRawMatrix 1 1 z₁ z₂ z₃ z₄)
      (karlssonRawMatrix 1 1 z₁ 1 z₃ z₄) := by
  rcases (sq_eq_one_iff).mp hz₂ with h | h
  · simpa [h] using equivalent_refl' (karlssonRawMatrix 1 1 z₁ 1 z₃ z₄)
  · simpa [h] using
      equivalent_karlssonRawMatrix_neg_z₂ 1 1 z₁ (-1) z₃ z₄

private theorem equivalent_normalize_z₃_to_omega
    {z₁ z₂ z₃ z₄ : ℂ} (hz₃ : z₃ ^ 2 = standardOmega ^ 2) :
    Equivalent (karlssonRawMatrix 1 1 z₁ z₂ z₃ z₄)
      (karlssonRawMatrix 1 1 z₁ z₂ standardOmega z₄) := by
  have hz : z₃ ^ 2 = standardOmega ^ 2 := hz₃
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz with h | h
  · simpa [h] using
      equivalent_refl'
        (karlssonRawMatrix 1 1 z₁ z₂ standardOmega z₄)
  · simpa [h] using
      equivalent_karlssonRawMatrix_neg_z₃
        1 1 z₁ z₂ (-standardOmega) z₄

private theorem equivalent_normalize_z₄_to_omega_sq
    {z₁ z₂ z₃ z₄ : ℂ} (hz₄ : z₄ ^ 2 = standardOmega) :
    Equivalent (karlssonRawMatrix 1 1 z₁ z₂ z₃ z₄)
      (karlssonRawMatrix 1 1 z₁ z₂ z₃ (standardOmega ^ 2)) := by
  have hz : z₄ ^ 2 = (standardOmega ^ 2) ^ 2 := by
    rw [standardOmega_fourth]
    exact hz₄
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz with h | h
  · simpa [h] using
      equivalent_refl'
        (karlssonRawMatrix 1 1 z₁ z₂ z₃ (standardOmega ^ 2))
  · simpa [h] using
      equivalent_karlssonRawMatrix_neg_z₄
        1 1 z₁ z₂ z₃ (-(standardOmega ^ 2))

private theorem equivalent_normalize_z₃_to_omega_sq
    {z₁ z₂ z₃ z₄ : ℂ} (hz₃ : z₃ ^ 2 = standardOmega) :
    Equivalent (karlssonRawMatrix 1 1 z₁ z₂ z₃ z₄)
      (karlssonRawMatrix 1 1 z₁ z₂ (standardOmega ^ 2) z₄) := by
  have hz : z₃ ^ 2 = (standardOmega ^ 2) ^ 2 := by
    rw [standardOmega_fourth]
    exact hz₃
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz with h | h
  · simpa [h] using
      equivalent_refl'
        (karlssonRawMatrix 1 1 z₁ z₂ (standardOmega ^ 2) z₄)
  · simpa [h] using
      equivalent_karlssonRawMatrix_neg_z₃
        1 1 z₁ z₂ (-(standardOmega ^ 2)) z₄

private theorem equivalent_normalize_z₄_to_omega
    {z₁ z₂ z₃ z₄ : ℂ} (hz₄ : z₄ ^ 2 = standardOmega ^ 2) :
    Equivalent (karlssonRawMatrix 1 1 z₁ z₂ z₃ z₄)
      (karlssonRawMatrix 1 1 z₁ z₂ z₃ standardOmega) := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz₄ with h | h
  · simpa [h] using
      equivalent_refl'
        (karlssonRawMatrix 1 1 z₁ z₂ z₃ standardOmega)
  · simpa [h] using
      equivalent_karlssonRawMatrix_neg_z₄
        1 1 z₁ z₂ z₃ (-standardOmega)

theorem karlssonRaw_one_one_isAffineFourierSeam
    {z₁ z₂ z₃ z₄ : ℂ}
    (hz₁ : Complex.normSq z₁ = 1)
    (hz₂ : Complex.normSq z₂ = 1)
    (hz₃ : Complex.normSq z₃ = 1)
    (hz₄ : Complex.normSq z₄ = 1)
    (hH : IsHadamard (karlssonRawMatrix 1 1 z₁ z₂ z₃ z₄)) :
    IsAffineFourierSeam (karlssonRawMatrix 1 1 z₁ z₂ z₃ z₄) := by
  rcases karlssonRaw_one_one_phase_alternatives
      hz₁ hz₂ hz₃ hz₄ hH with ⟨hA, hB, hC, hD⟩
  by_cases h₁ : z₁ ^ 2 = 1
  · by_cases h₂ : z₂ ^ 2 = 1
    · have heq₁ := equivalent_normalize_z₁_sign
          (z₂ := z₂) (z₃ := z₃) (z₄ := z₄) h₁
      have heq₂ := equivalent_normalize_z₂_sign
          (z₁ := 1) (z₃ := z₃) (z₄ := z₄) h₂
      have heq : Equivalent (karlssonRawMatrix 1 1 z₁ z₂ z₃ z₄)
          (karlssonRawMatrix 1 1 1 1 z₃ z₄) :=
        equivalent_trans heq₁ heq₂
      have hperm := equivalent_reindexMatrix (Equiv.refl I6)
        commonRightPlusPlusPermutation
        (karlssonRawMatrix 1 1 1 1 z₃ z₄)
      have htarget : Equivalent
          (karlssonRawMatrix 1 1 1 1 z₃ z₄)
          (affineFourierMatrix standardOmega z₃ z₄).transpose := by
        rw [common_right_plus_plus_eq_affine_transpose] at hperm
        exact hperm
      exact ⟨standardOmega, z₃, z₄,
        standardOmega_isPrimitiveCubicPhase, hz₃, hz₄,
        Or.inr (equivalent_trans heq htarget)⟩
    · have h₃ : z₃ ^ 2 = standardOmega ^ 2 := hB.resolve_left h₂
      have h₄ : z₄ ^ 2 = standardOmega := hD.resolve_left h₂
      have heq₁ := equivalent_normalize_z₁_sign
        (z₂ := z₂) (z₃ := z₃) (z₄ := z₄) h₁
      have heq₃ := equivalent_normalize_z₃_to_omega
        (z₁ := 1) (z₂ := z₂) (z₄ := z₄) h₃
      have heq₄ := equivalent_normalize_z₄_to_omega_sq
        (z₁ := 1) (z₂ := z₂) (z₃ := standardOmega) h₄
      have heq := equivalent_trans heq₁
        (equivalent_trans heq₃ heq₄)
      have hperm := equivalent_reindexMatrix (Equiv.refl I6)
        commonZ₁BranchPermutation
        (karlssonRawMatrix 1 1 1 z₂ standardOmega
          (standardOmega ^ 2))
      have htarget : Equivalent
          (karlssonRawMatrix 1 1 1 z₂ standardOmega
            (standardOmega ^ 2))
          (affineFourierMatrix standardOmega (-1) z₂) := by
        rw [common_z₁_branch_eq_affine] at hperm
        exact hperm
      exact ⟨standardOmega, -1, z₂,
        standardOmega_isPrimitiveCubicPhase, by norm_num, hz₂,
        Or.inl (equivalent_trans heq htarget)⟩
  · by_cases h₂ : z₂ ^ 2 = 1
    · have h₃ : z₃ ^ 2 = standardOmega := hA.resolve_left h₁
      have h₄ : z₄ ^ 2 = standardOmega ^ 2 := hC.resolve_left h₁
      have heq₂ := equivalent_normalize_z₂_sign
        (z₁ := z₁) (z₃ := z₃) (z₄ := z₄) h₂
      have heq₃ := equivalent_normalize_z₃_to_omega_sq
        (z₁ := z₁) (z₂ := 1) (z₄ := z₄) h₃
      have heq₄ := equivalent_normalize_z₄_to_omega
        (z₁ := z₁) (z₂ := 1) (z₃ := standardOmega ^ 2) h₄
      have heq := equivalent_trans heq₂
        (equivalent_trans heq₃ heq₄)
      have hperm := equivalent_reindexMatrix (Equiv.refl I6)
        commonZ₂BranchPermutation
        (karlssonRawMatrix 1 1 z₁ 1 (standardOmega ^ 2)
          standardOmega)
      have htarget : Equivalent
          (karlssonRawMatrix 1 1 z₁ 1 (standardOmega ^ 2)
            standardOmega)
          (affineFourierMatrix standardOmega z₁ (-1)) := by
        rw [common_z₂_branch_eq_affine] at hperm
        exact hperm
      exact ⟨standardOmega, z₁, -1,
        standardOmega_isPrimitiveCubicPhase, hz₁, by norm_num,
        Or.inl (equivalent_trans heq htarget)⟩
    · have h₃a : z₃ ^ 2 = standardOmega := hA.resolve_left h₁
      have h₃b : z₃ ^ 2 = standardOmega ^ 2 := hB.resolve_left h₂
      exact False.elim (standardOmega_sq_ne_standardOmega
        (h₃b.symm.trans h₃a))

end

end Hadamard6
