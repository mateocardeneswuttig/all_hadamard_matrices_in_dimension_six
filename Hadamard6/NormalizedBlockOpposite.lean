import Hadamard6.BlockNormalization
import Hadamard6.BlockOppositePair

/-!
# Opposite pairs after intrinsic block normalization
-/

namespace Hadamard6

def generalTwoByTwo (a b c d : ℂ) : Mat2 := !![a, b; c, d]

theorem generalTwoByTwo_isHadamard2
    {a b c d : ℂ}
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1) (hd : Complex.normSq d = 1)
    (hcross : a * star c + b * star d = 0) :
    IsHadamard2 (generalTwoByTwo a b c d) := by
  have hcross' : c * star a + d * star b = 0 := by
    have h := congrArg star hcross
    simp only [star_add, star_mul, star_zero, star_star] at h
    simpa [mul_comm] using h
  have hcrossE : a * (starRingEnd ℂ) c + b * (starRingEnd ℂ) d = 0 := by
    simpa only [starRingEnd_apply] using hcross
  have hcrossE' : c * (starRingEnd ℂ) a + d * (starRingEnd ℂ) b = 0 := by
    simpa only [starRingEnd_apply] using hcross'
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [generalTwoByTwo, ha, hb, hc, hd]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [generalTwoByTwo, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Complex.mul_conj, ha, hb, hc, hd,
        hcrossE, hcrossE'] <;> norm_num

theorem normalizedTopRight_opposite_hasHadamardTwoByTwo
    {H : Mat6} (hH : IsHadamard H)
    (hopp : HasOppositePairInNoninitialRow
      (normalizeFirstRow (Matrix.toBlocks₁₂ H))) :
    HasHadamardTwoByTwo H := by
  let B := Matrix.toBlocks₁₂ H
  rcases hopp with ⟨i, hi, j, k, hjk, hopp⟩
  let rows : I2 ↪ I6 := pairEmbedding (Sum.inl 0) (Sum.inl i)
    (by simpa using hi.symm)
  let cols : I2 ↪ I6 := pairEmbedding (Sum.inr j) (Sum.inr k)
    (by simpa using hjk)
  let a := B 0 j
  let b := B 0 k
  let c := B i j
  let d := B i k
  have ha : Complex.normSq a = 1 := hH.1 _ _
  have hb : Complex.normSq b = 1 := hH.1 _ _
  have hc : Complex.normSq c = 1 := hH.1 _ _
  have hd : Complex.normSq d = 1 := hH.1 _ _
  have hratio : star b * d = -(star a * c) := by
    simpa [normalizeFirstRow, a, b, c, d] using hopp
  have hcross : a * star c + b * star d = 0 := by
    have h := congrArg star hratio
    simp only [star_neg, star_mul, star_star] at h
    rw [show b * star d = -(a * star c) by simpa [mul_comm] using h]
    simp
  refine ⟨rows, cols, ?_⟩
  have heq : H.submatrix rows cols = generalTwoByTwo a b c d := by
    ext r s
    fin_cases r <;> fin_cases s <;> rfl
  rw [heq]
  exact generalTwoByTwo_isHadamard2 ha hb hc hd hcross

theorem normalizedTopLeft_opposite_hasHadamardTwoByTwo
    {H : Mat6} (hH : IsHadamard H)
    (hopp : HasOppositePairInNoninitialRow
      (normalizeFirstRow (Matrix.toBlocks₁₁ H))) :
    HasHadamardTwoByTwo H := by
  let E := Matrix.toBlocks₁₁ H
  rcases hopp with ⟨i, hi, j, k, hjk, hopp⟩
  let rows : I2 ↪ I6 := pairEmbedding (Sum.inl 0) (Sum.inl i)
    (by simpa using hi.symm)
  let cols : I2 ↪ I6 := pairEmbedding (Sum.inl j) (Sum.inl k)
    (by simpa using hjk)
  let a := E 0 j
  let b := E 0 k
  let c := E i j
  let d := E i k
  have ha : Complex.normSq a = 1 := hH.1 _ _
  have hb : Complex.normSq b = 1 := hH.1 _ _
  have hc : Complex.normSq c = 1 := hH.1 _ _
  have hd : Complex.normSq d = 1 := hH.1 _ _
  have hratio : star b * d = -(star a * c) := by
    simpa [normalizeFirstRow, a, b, c, d] using hopp
  have hcross : a * star c + b * star d = 0 := by
    have h := congrArg star hratio
    simp only [star_neg, star_mul, star_star] at h
    rw [show b * star d = -(a * star c) by simpa [mul_comm] using h]
    simp
  refine ⟨rows, cols, ?_⟩
  have heq : H.submatrix rows cols = generalTwoByTwo a b c d := by
    ext r s
    fin_cases r <;> fin_cases s <;> rfl
  rw [heq]
  exact generalTwoByTwo_isHadamard2 ha hb hc hd hcross

theorem normalizedBottomRight_oppositeColumn_hasHadamardTwoByTwo
    {H : Mat6} (hH : IsHadamard H)
    (hopp : HasOppositePairInNoninitialColumn
      (normalizeFirstColumn (Matrix.toBlocks₂₂ H))) :
    HasHadamardTwoByTwo H := by
  let D := Matrix.toBlocks₂₂ H
  rcases hopp with ⟨j, hj, i, k, hik, hopp⟩
  let rows : I2 ↪ I6 := pairEmbedding (Sum.inr i) (Sum.inr k)
    (by simpa using hik)
  let cols : I2 ↪ I6 := pairEmbedding (Sum.inr 0) (Sum.inr j)
    (by simpa using hj.symm)
  let a := D i 0
  let b := D i j
  let c := D k 0
  let d := D k j
  have ha : Complex.normSq a = 1 := hH.1 _ _
  have hb : Complex.normSq b = 1 := hH.1 _ _
  have hc : Complex.normSq c = 1 := hH.1 _ _
  have hd : Complex.normSq d = 1 := hH.1 _ _
  have hratio : star c * d = -(star a * b) := by
    simpa [normalizeFirstColumn, normalizeFirstRow, a, b, c, d] using hopp
  have hcross : a * star c + b * star d = 0 := by
    have haa : a * star a = 1 := by
      simpa [mul_comm] using star_mul_self_of_normSq_one ha
    have hcc : c * star c = 1 := by
      simpa [mul_comm] using star_mul_self_of_normSq_one hc
    have hdd : d * star d = 1 := by
      simpa [mul_comm] using star_mul_self_of_normSq_one hd
    have hdet : a * d = -(b * c) := by
      calc
        a * d = a * (c * star c) * d := by rw [hcc]; ring
        _ = (a * c) * (star c * d) := by ring
        _ = (a * c) * (-(star a * b)) := by rw [hratio]
        _ = -(b * c) := by
          rw [mul_neg]
          calc
            -(a * c * (star a * b)) = -((a * star a) * (b * c)) := by ring
            _ = -(b * c) := by rw [haa, one_mul]
    have hscale : (a * d + b * c) * (star c * star d) =
        a * star c + b * star d := by
      rw [add_mul]
      calc
        a * d * (star c * star d) + b * c * (star c * star d) =
            a * star c * (d * star d) +
              b * star d * (c * star c) := by ring
        _ = a * star c + b * star d := by rw [hdd, hcc, mul_one, mul_one]
    calc
      a * star c + b * star d =
          (a * d + b * c) * (star c * star d) := hscale.symm
      _ = 0 := by rw [hdet]; ring
  refine ⟨rows, cols, ?_⟩
  have heq : H.submatrix rows cols = generalTwoByTwo a b c d := by
    ext r s
    fin_cases r <;> fin_cases s <;> rfl
  rw [heq]
  exact generalTwoByTwo_isHadamard2 ha hb hc hd hcross

theorem normalizedBottomRight_oppositeRow_hasHadamardTwoByTwo
    {H : Mat6} (hH : IsHadamard H)
    (hopp : HasOppositePairInNoninitialRow
      (normalizeFirstRow (Matrix.toBlocks₂₂ H))) :
    HasHadamardTwoByTwo H := by
  let D := Matrix.toBlocks₂₂ H
  rcases hopp with ⟨i, hi, j, k, hjk, hopp⟩
  let rows : I2 ↪ I6 := pairEmbedding (Sum.inr 0) (Sum.inr i)
    (by simpa using hi.symm)
  let cols : I2 ↪ I6 := pairEmbedding (Sum.inr j) (Sum.inr k)
    (by simpa using hjk)
  let a := D 0 j
  let b := D 0 k
  let c := D i j
  let d := D i k
  have ha : Complex.normSq a = 1 := hH.1 _ _
  have hb : Complex.normSq b = 1 := hH.1 _ _
  have hc : Complex.normSq c = 1 := hH.1 _ _
  have hd : Complex.normSq d = 1 := hH.1 _ _
  have hratio : star b * d = -(star a * c) := by
    simpa [normalizeFirstRow, a, b, c, d] using hopp
  have hcross : a * star c + b * star d = 0 := by
    have h := congrArg star hratio
    simp only [star_neg, star_mul, star_star] at h
    rw [show b * star d = -(a * star c) by simpa [mul_comm] using h]
    simp
  refine ⟨rows, cols, ?_⟩
  have heq : H.submatrix rows cols = generalTwoByTwo a b c d := by
    ext r s
    fin_cases r <;> fin_cases s <;> rfl
  rw [heq]
  exact generalTwoByTwo_isHadamard2 ha hb hc hd hcross

theorem normalizedBottomLeft_oppositeColumn_hasHadamardTwoByTwo
    {H : Mat6} (hH : IsHadamard H)
    (hopp : HasOppositePairInNoninitialColumn
      (normalizeFirstColumn (Matrix.toBlocks₂₁ H))) :
    HasHadamardTwoByTwo H := by
  let C := Matrix.toBlocks₂₁ H
  rcases hopp with ⟨j, hj, i, k, hik, hopp⟩
  let rows : I2 ↪ I6 := pairEmbedding (Sum.inr i) (Sum.inr k)
    (by simpa using hik)
  let cols : I2 ↪ I6 := pairEmbedding (Sum.inl 0) (Sum.inl j)
    (by simpa using hj.symm)
  let a := C i 0
  let b := C i j
  let c := C k 0
  let d := C k j
  have ha : Complex.normSq a = 1 := hH.1 _ _
  have hb : Complex.normSq b = 1 := hH.1 _ _
  have hc : Complex.normSq c = 1 := hH.1 _ _
  have hd : Complex.normSq d = 1 := hH.1 _ _
  have hratio : star c * d = -(star a * b) := by
    simpa [normalizeFirstColumn, normalizeFirstRow, a, b, c, d] using hopp
  have hcross : a * star c + b * star d = 0 := by
    have haa : a * star a = 1 := by
      simpa [mul_comm] using star_mul_self_of_normSq_one ha
    have hcc : c * star c = 1 := by
      simpa [mul_comm] using star_mul_self_of_normSq_one hc
    have hdd : d * star d = 1 := by
      simpa [mul_comm] using star_mul_self_of_normSq_one hd
    have hdet : a * d = -(b * c) := by
      calc
        a * d = a * (c * star c) * d := by rw [hcc]; ring
        _ = (a * c) * (star c * d) := by ring
        _ = (a * c) * (-(star a * b)) := by rw [hratio]
        _ = -(b * c) := by
          rw [mul_neg]
          calc
            -(a * c * (star a * b)) = -((a * star a) * (b * c)) := by ring
            _ = -(b * c) := by rw [haa, one_mul]
    have hscale : (a * d + b * c) * (star c * star d) =
        a * star c + b * star d := by
      rw [add_mul]
      calc
        a * d * (star c * star d) + b * c * (star c * star d) =
            a * star c * (d * star d) + b * star d * (c * star c) := by ring
        _ = a * star c + b * star d := by rw [hdd, hcc, mul_one, mul_one]
    calc
      a * star c + b * star d =
          (a * d + b * c) * (star c * star d) := hscale.symm
      _ = 0 := by rw [hdet]; ring
  refine ⟨rows, cols, ?_⟩
  have heq : H.submatrix rows cols = generalTwoByTwo a b c d := by
    ext r s
    fin_cases r <;> fin_cases s <;> rfl
  rw [heq]
  exact generalTwoByTwo_isHadamard2 ha hb hc hd hcross

theorem normalizedTopLeft_oppositeColumn_hasHadamardTwoByTwo
    {H : Mat6} (hH : IsHadamard H)
    (hopp : HasOppositePairInNoninitialColumn
      (normalizeFirstColumn (Matrix.toBlocks₁₁ H))) :
    HasHadamardTwoByTwo H := by
  let E := Matrix.toBlocks₁₁ H
  rcases hopp with ⟨j, hj, i, k, hik, hopp⟩
  let rows : I2 ↪ I6 := pairEmbedding (Sum.inl i) (Sum.inl k)
    (by simpa using hik)
  let cols : I2 ↪ I6 := pairEmbedding (Sum.inl 0) (Sum.inl j)
    (by simpa using hj.symm)
  let a := E i 0
  let b := E i j
  let c := E k 0
  let d := E k j
  have ha : Complex.normSq a = 1 := hH.1 _ _
  have hb : Complex.normSq b = 1 := hH.1 _ _
  have hc : Complex.normSq c = 1 := hH.1 _ _
  have hd : Complex.normSq d = 1 := hH.1 _ _
  have hratio : star c * d = -(star a * b) := by
    simpa [normalizeFirstColumn, normalizeFirstRow, a, b, c, d] using hopp
  have hcross : a * star c + b * star d = 0 := by
    have haa : a * star a = 1 := by
      simpa [mul_comm] using star_mul_self_of_normSq_one ha
    have hcc : c * star c = 1 := by
      simpa [mul_comm] using star_mul_self_of_normSq_one hc
    have hdd : d * star d = 1 := by
      simpa [mul_comm] using star_mul_self_of_normSq_one hd
    have hdet : a * d = -(b * c) := by
      calc
        a * d = a * (c * star c) * d := by rw [hcc]; ring
        _ = (a * c) * (star c * d) := by ring
        _ = (a * c) * (-(star a * b)) := by rw [hratio]
        _ = -(b * c) := by
          rw [mul_neg]
          calc
            -(a * c * (star a * b)) = -((a * star a) * (b * c)) := by ring
            _ = -(b * c) := by rw [haa, one_mul]
    have hscale : (a * d + b * c) * (star c * star d) =
        a * star c + b * star d := by
      rw [add_mul]
      calc
        a * d * (star c * star d) + b * c * (star c * star d) =
            a * star c * (d * star d) + b * star d * (c * star c) := by ring
        _ = a * star c + b * star d := by rw [hdd, hcc, mul_one, mul_one]
    calc
      a * star c + b * star d =
          (a * d + b * c) * (star c * star d) := hscale.symm
      _ = 0 := by rw [hdet]; ring
  refine ⟨rows, cols, ?_⟩
  have heq : H.submatrix rows cols = generalTwoByTwo a b c d := by
    ext r s
    fin_cases r <;> fin_cases s <;> rfl
  rw [heq]
  exact generalTwoByTwo_isHadamard2 ha hb hc hd hcross

end Hadamard6
