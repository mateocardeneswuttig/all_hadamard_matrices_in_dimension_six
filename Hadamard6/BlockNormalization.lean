import Hadamard6.ColumnFibreSymmetry

/-!
# Normalizing an individual `3 x 3` block

Column phases normalize a block's first row without changing its row Gram
matrix.  Dually, row phases normalize the first column without changing the
column Gram matrix.  This lets the fibre theorem be applied after block
switches without repeatedly dephasing the whole order-six matrix.
-/

namespace Hadamard6

def normalizeFirstRow (X : Mat3) : Mat3 :=
  fun i j ↦ star (X 0 j) * X i j

theorem normalizeFirstRow_entrywiseUnit {X : Mat3}
    (hX : EntrywiseUnit X) : EntrywiseUnit (normalizeFirstRow X) := by
  intro i j
  rw [show normalizeFirstRow X i j =
      star (X 0 j) * X i j by rfl,
    Complex.normSq_mul]
  have hs : Complex.normSq (star (X 0 j)) = 1 := by
    rw [Complex.star_def, Complex.normSq_conj, hX 0 j]
  rw [hs, hX i j]
  norm_num

theorem normalizeFirstRow_firstRow {X : Mat3}
    (hX : EntrywiseUnit X) : ∀ j, normalizeFirstRow X 0 j = 1 := by
  intro j
  exact star_mul_self_of_normSq_one (hX 0 j)

theorem normalizeFirstRow_rowGram {X : Mat3}
    (hX : EntrywiseUnit X) :
    normalizeFirstRow X * Matrix.conjTranspose (normalizeFirstRow X) =
      X * Matrix.conjTranspose X := by
  have h0 := star_mul_self_of_normSq_one (hX 0 0)
  have h1 := star_mul_self_of_normSq_one (hX 0 1)
  have h2 := star_mul_self_of_normSq_one (hX 0 2)
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    normalizeFirstRow, star_mul, Fin.sum_univ_three]
  calc
    _ = (star (X 0 0) * X 0 0) * (X i 0 * star (X j 0)) +
        (star (X 0 1) * X 0 1) * (X i 1 * star (X j 1)) +
        (star (X 0 2) * X 0 2) * (X i 2 * star (X j 2)) := by
        simp only [star_star]
        ring
    _ = X i 0 * star (X j 0) + X i 1 * star (X j 1) +
        X i 2 * star (X j 2) := by rw [h0, h1, h2]; ring

theorem normalizeFirstRow_det {X : Mat3} :
    (normalizeFirstRow X).det =
      (star (X 0 0) * star (X 0 1) * star (X 0 2)) * X.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  simp only [normalizeFirstRow]
  ring

theorem normalizeFirstRow_det_ne_zero {X : Mat3}
    (hX : EntrywiseUnit X) (hdet : X.det ≠ 0) :
    (normalizeFirstRow X).det ≠ 0 := by
  rw [normalizeFirstRow_det]
  apply mul_ne_zero
  · repeat' apply mul_ne_zero
    all_goals
      intro h
      have := hX 0 0
      try have := hX 0 1
      try have := hX 0 2
      simp_all
  · exact hdet

theorem normalizeFirstRow_mem_fibre {G X : Mat3}
    (hX : EntrywiseUnit X)
    (hgram : X * Matrix.conjTranspose X = G) :
    normalizeFirstRow X ∈ normalizedRowGramFibre G := by
  exact ⟨normalizeFirstRow_entrywiseUnit hX,
    normalizeFirstRow_firstRow hX,
    (normalizeFirstRow_rowGram hX).trans hgram⟩

theorem normalizeFirstRow_isHadamard3_iff {X : Mat3}
    (hX : EntrywiseUnit X) :
    IsHadamard3 (normalizeFirstRow X) ↔ IsHadamard3 X := by
  rw [IsHadamard3, IsHadamard3]
  simp [normalizeFirstRow_entrywiseUnit hX, hX,
    normalizeFirstRow_rowGram hX]

theorem rowTau_normalizeFirstRow {X : Mat3} (hX : EntrywiseUnit X) :
    rowTau (normalizeFirstRow X) = rowTau X := by
  rw [rowTau, normalizeFirstRow_rowGram hX]
  rfl

def normalizeFirstColumn (X : Mat3) : Mat3 :=
  (normalizeFirstRow X.transpose).transpose

theorem normalizeFirstColumn_entrywiseUnit {X : Mat3}
    (hX : EntrywiseUnit X) : EntrywiseUnit (normalizeFirstColumn X) := by
  intro i j
  exact normalizeFirstRow_entrywiseUnit (fun a b ↦ hX b a) j i

theorem normalizeFirstColumn_firstColumn {X : Mat3}
    (hX : EntrywiseUnit X) : ∀ i, normalizeFirstColumn X i 0 = 1 := by
  intro i
  exact normalizeFirstRow_firstRow (fun a b ↦ hX b a) i

theorem normalizeFirstColumn_columnGram {X : Mat3}
    (hX : EntrywiseUnit X) :
    Matrix.conjTranspose (normalizeFirstColumn X) * normalizeFirstColumn X =
      Matrix.conjTranspose X * X := by
  have hrow := normalizeFirstRow_rowGram (X := X.transpose)
    (fun i j ↦ hX j i)
  have ht := congrArg Matrix.transpose hrow
  have hxct : (Matrix.conjTranspose X.transpose).transpose =
      Matrix.conjTranspose X := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hnct :
      (Matrix.conjTranspose (normalizeFirstRow X.transpose)).transpose =
        Matrix.conjTranspose (normalizeFirstRow X.transpose).transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [Matrix.transpose_mul] at ht
  rw [Matrix.transpose_mul] at ht
  rw [hxct] at ht
  rw [hnct] at ht
  simpa [normalizeFirstColumn] using ht

theorem normalizeFirstColumn_det_ne_zero {X : Mat3}
    (hX : EntrywiseUnit X) (hdet : X.det ≠ 0) :
    (normalizeFirstColumn X).det ≠ 0 := by
  simpa [normalizeFirstColumn] using
    normalizeFirstRow_det_ne_zero (X := X.transpose)
      (fun i j ↦ hX j i) (by simpa using hdet)

theorem normalizeFirstColumn_mem_fibre {G X : Mat3}
    (hX : EntrywiseUnit X)
    (hgram : Matrix.conjTranspose X * X = G) :
    normalizeFirstColumn X ∈ normalizedColumnGramFibre G := by
  exact ⟨normalizeFirstColumn_entrywiseUnit hX,
    normalizeFirstColumn_firstColumn hX,
    (normalizeFirstColumn_columnGram hX).trans hgram⟩

theorem normalizeFirstColumn_isHadamard3_iff {X : Mat3}
    (hX : EntrywiseUnit X) :
    IsHadamard3 (normalizeFirstColumn X) ↔ IsHadamard3 X := by
  rw [← transpose_isHadamard3_iff (X := normalizeFirstColumn X),
    ← transpose_isHadamard3_iff (X := X)]
  simpa [normalizeFirstColumn] using
    normalizeFirstRow_isHadamard3_iff (X := X.transpose)
      (fun i j ↦ hX j i)

theorem columnTau_normalizeFirstColumn_re {X : Mat3}
    (hX : EntrywiseUnit X) :
    (columnTau (normalizeFirstColumn X)).re = (columnTau X).re := by
  rw [← rowTau_transpose_re, ← rowTau_transpose_re]
  simpa [normalizeFirstColumn] using congrArg Complex.re
    (rowTau_normalizeFirstRow (X := X.transpose) (fun i j ↦ hX j i))

end Hadamard6
