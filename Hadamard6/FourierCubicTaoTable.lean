import Hadamard6.FourierCubicTaoCases0
import Hadamard6.FourierCubicTaoCases1
import Hadamard6.FourierCubicTaoCases2

/-!
# Assembly of the finite Tao table

The expensive entrywise checks live in three bounded modules.  This file only
dispatches a row index and turns the resulting matrix equality into ordinary
Hadamard equivalence.
-/

namespace Hadamard6

noncomputable section

theorem cubicTaoTable_dephased_eq
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega)
    (n : CubicTaoRow) :
    dephase (reindexMatrix (Equiv.refl I6) (cubicTaoPermutation n)
      (fourierNormalForm omega (cubicTaoP omega n)
        (cubicTaoQ omega n) (cubicTaoR omega n) (cubicTaoS omega n)
        (fourierForcedD omega (cubicTaoP omega n)
          (cubicTaoQ omega n) (cubicTaoR omega n)
          (cubicTaoS omega n)))) =
      taoMatrix (cubicTaoTarget omega n) := by
  change CubicTaoCertificate omega n
  fin_cases n
  · exact cubicTaoCase0_dephased_eq homega
  · exact cubicTaoCase1_dephased_eq homega
  · exact cubicTaoCase2_dephased_eq homega
  · exact cubicTaoCase3_dephased_eq homega
  · exact cubicTaoCase4_dephased_eq homega
  · exact cubicTaoCase5_dephased_eq homega
  · exact cubicTaoCase6_dephased_eq homega
  · exact cubicTaoCase7_dephased_eq homega
  · exact cubicTaoCase8_dephased_eq homega
  · exact cubicTaoCase9_dephased_eq homega
  · exact cubicTaoCase10_dephased_eq homega
  · exact cubicTaoCase11_dephased_eq homega
  · exact cubicTaoCase12_dephased_eq homega
  · exact cubicTaoCase13_dephased_eq homega
  · exact cubicTaoCase14_dephased_eq homega
  · exact cubicTaoCase15_dephased_eq homega
  · exact cubicTaoCase16_dephased_eq homega
  · exact cubicTaoCase17_dephased_eq homega

/-- Every row of the explicit table is in Tao's equivalence orbit. -/
theorem cubicTaoTable_isTaoOrbit
    {omega : ℂ} (homega : IsPrimitiveCubicPhase omega)
    (n : CubicTaoRow)
    (hH : IsHadamard
      (fourierNormalForm omega (cubicTaoP omega n)
        (cubicTaoQ omega n) (cubicTaoR omega n) (cubicTaoS omega n)
        (fourierForcedD omega (cubicTaoP omega n)
          (cubicTaoQ omega n) (cubicTaoR omega n)
          (cubicTaoS omega n)))) :
    IsTaoOrbit
      (fourierNormalForm omega (cubicTaoP omega n)
        (cubicTaoQ omega n) (cubicTaoR omega n) (cubicTaoS omega n)
        (fourierForcedD omega (cubicTaoP omega n)
          (cubicTaoQ omega n) (cubicTaoR omega n)
          (cubicTaoS omega n))) :=
  isTaoOrbit_of_dephased_column_permutation
    (cubicTaoPermutation n) hH (cubicTaoTarget_primitive homega n)
    (cubicTaoTable_dephased_eq homega n)

end

end Hadamard6

