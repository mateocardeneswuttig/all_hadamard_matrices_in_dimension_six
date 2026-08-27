import Hadamard6.EquivalentStrata
import Hadamard6.TaoOrbit

/-!
# Concrete finite-corner endpoint for order six

This module fixes the concrete exceptional-sector predicates used by the
paper-facing theorem.  The Karlsson sector is represented intrinsically by
the `2 x 2` Hadamard condition, while the Tao sector is the explicit orbit
defined in `TaoOrbit.lean`.
-/

namespace Hadamard6

/-- The intrinsic Karlsson sector on raw matrices.  Including Hadamardness in
the definition makes sector soundness immediate and avoids assigning the
Karlsson name to arbitrary non-Hadamard matrices containing an accidental
`2 x 2` Hadamard submatrix. -/
def IsKarlssonConcrete (H : Mat6) : Prop :=
  IsHadamard H ∧ HasHadamardTwoByTwo H

/-- Intrinsic Karlsson membership is constant on equivalence classes. -/
theorem equivalent_isKarlssonConcrete_iff {H K : Mat6}
    (hHK : Equivalent H K) :
    IsKarlssonConcrete H ↔ IsKarlssonConcrete K := by
  simp only [IsKarlssonConcrete]
  exact and_congr (equivalent_isHadamard_iff hHK)
    (equivalent_hasHadamardTwoByTwo_iff hHK)

end Hadamard6
