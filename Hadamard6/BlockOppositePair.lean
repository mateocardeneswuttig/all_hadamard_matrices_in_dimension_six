import Hadamard6.ColumnFibreSymmetry
import Hadamard6.Strata
import Mathlib.Tactic.FinCases

/-!
# Opposite pairs inside normalized blocks

An opposite pair in a block whose first row (or first column) is normalized
exhibits a literal Hadamard `2 x 2` submatrix of the ambient matrix.
-/

namespace Hadamard6

def pairEmbedding {α : Type} (a b : α) (hab : a ≠ b) : I2 ↪ α where
  toFun := Fin.cases a (fun _ ↦ b)
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · change a = b at h
      exact (hab h).elim
    · change b = a at h
      exact (hab h.symm).elim
    · rfl

@[simp] theorem pairEmbedding_zero {α : Type} (a b : α) (hab : a ≠ b) :
    pairEmbedding a b hab 0 = a := by
  rfl

@[simp] theorem pairEmbedding_one {α : Type} (a b : α) (hab : a ≠ b) :
    pairEmbedding a b hab 1 = b := by
  rfl

def rowHadamard2 (z : ℂ) : Mat2 := !![1, 1; z, -z]
def columnHadamard2 (z : ℂ) : Mat2 := !![1, z; 1, -z]

theorem rowHadamard2_isHadamard2 {z : ℂ}
    (hz : Complex.normSq z = 1) : IsHadamard2 (rowHadamard2 z) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [rowHadamard2, hz]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rowHadamard2, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Complex.mul_conj, hz] <;> norm_num

theorem columnHadamard2_isHadamard2 {z : ℂ}
    (hz : Complex.normSq z = 1) : IsHadamard2 (columnHadamard2 z) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [columnHadamard2, hz]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [columnHadamard2, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Complex.mul_conj, hz] <;> norm_num

theorem topRight_oppositePair_hasHadamardTwoByTwo
    {H : Mat6} (hH : IsHadamard H) (hdeph : IsDephased H)
    (hopp : HasOppositePairInNoninitialRow (Matrix.toBlocks₁₂ H)) :
    HasHadamardTwoByTwo H := by
  rcases hopp with ⟨i, hi, j, k, hjk, hopp⟩
  let rows : I2 ↪ I6 := pairEmbedding (Sum.inl 0) (Sum.inl i)
    (by simpa using hi.symm)
  let cols : I2 ↪ I6 := pairEmbedding (Sum.inr j) (Sum.inr k)
    (by simpa using hjk)
  let z := H (Sum.inl i) (Sum.inr j)
  have hz : Complex.normSq z = 1 := hH.1 _ _
  refine ⟨rows, cols, ?_⟩
  have heq : H.submatrix rows cols = rowHadamard2 z := by
    ext r c
    fin_cases r <;> fin_cases c
    · change H (Sum.inl 0) (Sum.inr j) = 1
      exact hdeph.1 _
    · change H (Sum.inl 0) (Sum.inr k) = 1
      exact hdeph.1 _
    · rfl
    · change H (Sum.inl i) (Sum.inr k) = -H (Sum.inl i) (Sum.inr j)
      simpa [Matrix.toBlocks₁₂] using hopp
  rw [heq]
  exact rowHadamard2_isHadamard2 hz

theorem topLeft_oppositePair_hasHadamardTwoByTwo
    {H : Mat6} (hH : IsHadamard H) (hdeph : IsDephased H)
    (hopp : HasOppositePairInNoninitialRow (Matrix.toBlocks₁₁ H)) :
    HasHadamardTwoByTwo H := by
  rcases hopp with ⟨i, hi, j, k, hjk, hopp⟩
  let rows : I2 ↪ I6 := pairEmbedding (Sum.inl 0) (Sum.inl i)
    (by simpa using hi.symm)
  let cols : I2 ↪ I6 := pairEmbedding (Sum.inl j) (Sum.inl k)
    (by simpa using hjk)
  let z := H (Sum.inl i) (Sum.inl j)
  have hz : Complex.normSq z = 1 := hH.1 _ _
  refine ⟨rows, cols, ?_⟩
  have heq : H.submatrix rows cols = rowHadamard2 z := by
    ext r c
    fin_cases r <;> fin_cases c
    · change H (Sum.inl 0) (Sum.inl j) = 1
      exact hdeph.1 _
    · change H (Sum.inl 0) (Sum.inl k) = 1
      exact hdeph.1 _
    · rfl
    · change H (Sum.inl i) (Sum.inl k) = -H (Sum.inl i) (Sum.inl j)
      simpa [Matrix.toBlocks₁₁] using hopp
  rw [heq]
  exact rowHadamard2_isHadamard2 hz

theorem bottomRight_oppositeColumn_hasHadamardTwoByTwo
    {H : Mat6} (hH : IsHadamard H)
    (hfirst : ∀ i, Matrix.toBlocks₂₂ H i 0 = 1)
    (hopp : HasOppositePairInNoninitialColumn (Matrix.toBlocks₂₂ H)) :
    HasHadamardTwoByTwo H := by
  rcases hopp with ⟨j, hj, i, k, hik, hopp⟩
  let rows : I2 ↪ I6 := pairEmbedding (Sum.inr i) (Sum.inr k)
    (by simpa using hik)
  let cols : I2 ↪ I6 := pairEmbedding (Sum.inr 0) (Sum.inr j)
    (by simpa using hj.symm)
  let z := H (Sum.inr i) (Sum.inr j)
  have hz : Complex.normSq z = 1 := hH.1 _ _
  refine ⟨rows, cols, ?_⟩
  have heq : H.submatrix rows cols = columnHadamard2 z := by
    ext r c
    fin_cases r <;> fin_cases c
    · change H (Sum.inr i) (Sum.inr 0) = 1
      simpa [Matrix.toBlocks₂₂] using hfirst i
    · rfl
    · change H (Sum.inr k) (Sum.inr 0) = 1
      simpa [Matrix.toBlocks₂₂] using hfirst k
    · change H (Sum.inr k) (Sum.inr j) = -H (Sum.inr i) (Sum.inr j)
      simpa [Matrix.toBlocks₂₂] using hopp
  rw [heq]
  exact columnHadamard2_isHadamard2 hz

end Hadamard6
