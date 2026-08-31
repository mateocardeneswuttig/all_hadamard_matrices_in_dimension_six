import Hadamard6.FourierCoreFromNormalization
import Hadamard6.TaoOrbit

/-!
# Classification of the cubic simultaneous-Fourier chart

The all-Fourier branch of the classification proof reaches a stronger
normal form than the general cubic-row-and-column criterion: three blocks
are explicit Fourier gauges, the fourth block is forced, and the four gauge
phases are cubic roots.  This file classifies that finite chart directly.

The conceptual alternatives are visible here.  A `-1` in the first row of
the forced fourth block gives an explicit Hadamard `2 x 2` submatrix.  The
remaining physical cases are transported, by an explicit column
permutation and ordinary dephasing, to Tao's matrix.  Algebraically
impossible phase tuples are rejected by the entrywise-unit condition.
-/

namespace Hadamard6

noncomputable section

/-- A `-1` in the first row of the forced fourth block gives the displayed
Hadamard `2 x 2` submatrix using the first row and column of the dephased
Fourier normal form. -/
theorem fourierNormalForm_hasTwoByTwo_of_D_entry_neg_one
    {omega p q r s : ℂ} {D : Mat3} {k : I3}
    (hk : D 0 k = -1) :
    HasHadamardTwoByTwo (fourierNormalForm omega p q r s D) := by
  let rows : I2 ↪ I6 :=
    pairEmbedding (Sum.inl 0) (Sum.inr 0) (by simp)
  let cols : I2 ↪ I6 :=
    pairEmbedding (Sum.inl 0) (Sum.inr k) (by simp)
  refine ⟨rows, cols, ?_⟩
  have heq :
      (fourierNormalForm omega p q r s D).submatrix rows cols =
        rowHadamard2 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rows, cols, fourierNormalForm, fourier3, rowGauge,
        columnGauge, fourierParameters, rowHadamard2, hk]
  rw [heq]
  exact rowHadamard2_isHadamard2 (by norm_num)

/-- A zero entry in the forced fourth block contradicts physicality.  This
is the only fact needed to reject the algebraically possible but
non-unimodular cubic phase tuples. -/
theorem false_of_fourierForcedD_entry_zero
    {omega p q r s : ℂ} {i j : I3}
    (hH : IsHadamard (fourierNormalForm omega p q r s
      (fourierForcedD omega p q r s)))
    (hzero : fourierForcedD omega p q r s i j = 0) : False := by
  have hentry := hH.1 (Sum.inr i) (Sum.inr j)
  simp [fourierNormalForm, hzero] at hentry

def cubicIndex0 : I6 := Sum.inl 0
def cubicIndex1 : I6 := Sum.inl 1
def cubicIndex2 : I6 := Sum.inl 2
def cubicIndex3 : I6 := Sum.inr 0
def cubicIndex4 : I6 := Sum.inr 1
def cubicIndex5 : I6 := Sum.inr 2

/-- Six displayed images, used only to record the small column-permutation
table in the Tao certificate. -/
def sixMap (a0 a1 a2 a3 a4 a5 : I6) : I6 → I6
  | Sum.inl i =>
      Fin.cases a0 (fun i' => Fin.cases a1 (fun _ => a2) i') i
  | Sum.inr i =>
      Fin.cases a3 (fun i' => Fin.cases a4 (fun _ => a5) i') i

def sixPermutation (a0 a1 a2 a3 a4 a5 : I6)
    (h : Function.Bijective (sixMap a0 a1 a2 a3 a4 a5)) :
    Equiv.Perm I6 :=
  Equiv.ofBijective _ h

@[simp] theorem sixPermutation_inl_zero
    (a0 a1 a2 a3 a4 a5 : I6)
    (h : Function.Bijective (sixMap a0 a1 a2 a3 a4 a5)) :
    sixPermutation a0 a1 a2 a3 a4 a5 h (Sum.inl 0) = a0 := rfl

@[simp] theorem sixPermutation_inl_one
    (a0 a1 a2 a3 a4 a5 : I6)
    (h : Function.Bijective (sixMap a0 a1 a2 a3 a4 a5)) :
    sixPermutation a0 a1 a2 a3 a4 a5 h (Sum.inl 1) = a1 := rfl

@[simp] theorem sixPermutation_inl_two
    (a0 a1 a2 a3 a4 a5 : I6)
    (h : Function.Bijective (sixMap a0 a1 a2 a3 a4 a5)) :
    sixPermutation a0 a1 a2 a3 a4 a5 h (Sum.inl 2) = a2 := rfl

@[simp] theorem sixPermutation_inr_zero
    (a0 a1 a2 a3 a4 a5 : I6)
    (h : Function.Bijective (sixMap a0 a1 a2 a3 a4 a5)) :
    sixPermutation a0 a1 a2 a3 a4 a5 h (Sum.inr 0) = a3 := rfl

@[simp] theorem sixPermutation_inr_one
    (a0 a1 a2 a3 a4 a5 : I6)
    (h : Function.Bijective (sixMap a0 a1 a2 a3 a4 a5)) :
    sixPermutation a0 a1 a2 a3 a4 a5 h (Sum.inr 1) = a4 := rfl

@[simp] theorem sixPermutation_inr_two
    (a0 a1 a2 a3 a4 a5 : I6)
    (h : Function.Bijective (sixMap a0 a1 a2 a3 a4 a5)) :
    sixPermutation a0 a1 a2 a3 a4 a5 h (Sum.inr 2) = a5 := rfl

/-- A checked dephased column permutation is an ordinary equivalence to
Tao's matrix.  The finite certificate below only has to prove the displayed
matrix equality. -/
theorem isTaoOrbit_of_dephased_column_permutation
    {H : Mat6} {omega : ℂ} (tau : Equiv.Perm I6)
    (hH : IsHadamard H) (homega : IsPrimitiveCubicPhase omega)
    (heq : dephase (reindexMatrix (Equiv.refl I6) tau H) =
      taoMatrix omega) : IsTaoOrbit H := by
  have hperm : Equivalent H
      (reindexMatrix (Equiv.refl I6) tau H) :=
    equivalent_reindexMatrix _ _ _
  have hunit : EntrywiseUnit
      (reindexMatrix (Equiv.refl I6) tau H) := by
    intro i j
    exact hH.1 _ _
  have hdep : Equivalent
      (reindexMatrix (Equiv.refl I6) tau H)
      (dephase (reindexMatrix (Equiv.refl I6) tau H)) :=
    equivalent_dephase hunit
  exact ⟨omega, homega, by
    rw [← heq]
    exact equivalent_trans hperm hdep⟩

private def cubicTaoPerm034152 : Equiv.Perm I6 :=
  sixPermutation cubicIndex0 cubicIndex3 cubicIndex4 cubicIndex1
    cubicIndex5 cubicIndex2 (by decide)

structure CubicPowerFacts (omega : ℂ) : Prop where
  cube : omega ^ 3 = 1
  fourth : omega ^ 4 = omega
  fifth : omega ^ 5 = omega ^ 2
  sixth : omega ^ 6 = 1
  seventh : omega ^ 7 = omega
  eighth : omega ^ 8 = omega ^ 2

theorem cubicPowerFacts {omega : ℂ}
    (homega : IsPrimitiveCubicPhase omega) : CubicPowerFacts omega := by
  have h3 : omega ^ 3 = 1 := primitiveCubicPhase_cube homega
  have h4 : omega ^ 4 = omega := by
    calc
      omega ^ 4 = omega * omega ^ 3 := by ring
      _ = omega := by rw [h3, mul_one]
  have h5 : omega ^ 5 = omega ^ 2 := by
    calc
      omega ^ 5 = omega ^ 2 * omega ^ 3 := by ring
      _ = omega ^ 2 := by rw [h3, mul_one]
  have h6 : omega ^ 6 = 1 := by
    rw [show omega ^ 6 = (omega ^ 3) ^ 2 by ring, h3]
    norm_num
  have h7 : omega ^ 7 = omega := by
    rw [show omega ^ 7 = omega * omega ^ 6 by ring, h6, mul_one]
  have h8 : omega ^ 8 = omega ^ 2 := by
    rw [show omega ^ 8 = omega ^ 2 * omega ^ 6 by ring, h6, mul_one]
  exact ⟨h3, h4, h5, h6, h7, h8⟩

theorem primitiveCubicPhase_square {omega : ℂ}
    (homega : IsPrimitiveCubicPhase omega) :
    IsPrimitiveCubicPhase (omega ^ 2) := by
  have h4 : omega ^ 4 = omega := (cubicPowerFacts homega).fourth
  refine ⟨primitiveCubicPhase_sq_norm homega, ?_⟩
  rw [show (omega ^ 2) ^ 2 = omega ^ 4 by ring, h4]
  linear_combination homega.2

abbrev CubicTaoRow := Fin 18

def cubicTaoP (omega : ℂ) : CubicTaoRow → ℂ := ![
  1, 1, 1, 1, 1, 1,
  omega, omega, omega, omega, omega, omega,
  omega ^ 2, omega ^ 2, omega ^ 2,
  omega ^ 2, omega ^ 2, omega ^ 2]

def cubicTaoQ (omega : ℂ) : CubicTaoRow → ℂ := ![
  omega, omega, omega, omega ^ 2, omega ^ 2, omega ^ 2,
  1, 1, 1, omega, omega, omega,
  1, 1, 1,
  omega ^ 2, omega ^ 2, omega ^ 2]

def cubicTaoR (omega : ℂ) : CubicTaoRow → ℂ := ![
  1, omega, omega ^ 2, 1, omega, omega ^ 2,
  1, omega, omega ^ 2, 1, omega, omega ^ 2,
  1, omega, omega ^ 2,
  1, omega, omega ^ 2]

def cubicTaoS (omega : ℂ) : CubicTaoRow → ℂ := ![
  omega ^ 2, omega, 1, omega, 1, omega ^ 2,
  omega ^ 2, omega, 1, omega, 1, omega ^ 2,
  omega, 1, omega ^ 2,
  omega ^ 2, omega, 1]

def cubicTaoTarget (omega : ℂ) : CubicTaoRow → ℂ := ![
  omega, omega, omega, omega ^ 2, omega ^ 2, omega ^ 2,
  omega, omega, omega, omega ^ 2, omega ^ 2, omega ^ 2,
  omega ^ 2, omega ^ 2, omega ^ 2,
  omega, omega, omega]

def cubicTaoPermutation : CubicTaoRow → Equiv.Perm I6 := ![
  sixPermutation cubicIndex0 cubicIndex3 cubicIndex4 cubicIndex1 cubicIndex5 cubicIndex2 (by decide),
  sixPermutation cubicIndex1 cubicIndex4 cubicIndex5 cubicIndex2 cubicIndex3 cubicIndex0 (by decide),
  sixPermutation cubicIndex2 cubicIndex5 cubicIndex3 cubicIndex0 cubicIndex4 cubicIndex1 (by decide),
  sixPermutation cubicIndex1 cubicIndex4 cubicIndex3 cubicIndex0 cubicIndex5 cubicIndex2 (by decide),
  sixPermutation cubicIndex0 cubicIndex3 cubicIndex5 cubicIndex2 cubicIndex4 cubicIndex1 (by decide),
  sixPermutation cubicIndex2 cubicIndex5 cubicIndex4 cubicIndex1 cubicIndex3 cubicIndex0 (by decide),
  sixPermutation cubicIndex0 cubicIndex5 cubicIndex3 cubicIndex1 cubicIndex4 cubicIndex2 (by decide),
  sixPermutation cubicIndex1 cubicIndex3 cubicIndex4 cubicIndex2 cubicIndex5 cubicIndex0 (by decide),
  sixPermutation cubicIndex2 cubicIndex4 cubicIndex5 cubicIndex0 cubicIndex3 cubicIndex1 (by decide),
  sixPermutation cubicIndex1 cubicIndex3 cubicIndex5 cubicIndex0 cubicIndex4 cubicIndex2 (by decide),
  sixPermutation cubicIndex0 cubicIndex5 cubicIndex4 cubicIndex2 cubicIndex3 cubicIndex1 (by decide),
  sixPermutation cubicIndex2 cubicIndex4 cubicIndex3 cubicIndex1 cubicIndex5 cubicIndex0 (by decide),
  sixPermutation cubicIndex1 cubicIndex5 cubicIndex4 cubicIndex0 cubicIndex3 cubicIndex2 (by decide),
  sixPermutation cubicIndex0 cubicIndex4 cubicIndex3 cubicIndex2 cubicIndex5 cubicIndex1 (by decide),
  sixPermutation cubicIndex2 cubicIndex3 cubicIndex5 cubicIndex1 cubicIndex4 cubicIndex0 (by decide),
  sixPermutation cubicIndex0 cubicIndex4 cubicIndex5 cubicIndex1 cubicIndex3 cubicIndex2 (by decide),
  sixPermutation cubicIndex1 cubicIndex5 cubicIndex3 cubicIndex2 cubicIndex4 cubicIndex0 (by decide),
  sixPermutation cubicIndex2 cubicIndex3 cubicIndex4 cubicIndex0 cubicIndex5 cubicIndex1 (by decide)]

/-- The matrix equality certified by one row of the finite Tao table. -/
def CubicTaoCertificate (omega : ℂ) (n : CubicTaoRow) : Prop :=
  dephase (reindexMatrix (Equiv.refl I6) (cubicTaoPermutation n)
    (fourierNormalForm omega (cubicTaoP omega n)
      (cubicTaoQ omega n) (cubicTaoR omega n) (cubicTaoS omega n)
      (fourierForcedD omega (cubicTaoP omega n)
        (cubicTaoQ omega n) (cubicTaoR omega n)
        (cubicTaoS omega n)))) =
    taoMatrix (cubicTaoTarget omega n)

theorem cubicTaoTarget_primitive
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega)
    (n : CubicTaoRow) :
    IsPrimitiveCubicPhase (cubicTaoTarget omega n) := by
  fin_cases n <;> simp [cubicTaoTarget] <;>
    first | exact homega | exact primitiveCubicPhase_square homega

end


end Hadamard6
