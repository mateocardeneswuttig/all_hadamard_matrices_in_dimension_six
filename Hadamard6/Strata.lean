import Hadamard6.Basic

/-!
# Geometric predicates used by the classification
-/

namespace Hadamard6

def HasHadamardTwoByTwo (H : Mat6) : Prop :=
  ∃ (rows cols : I2 ↪ I6),
    IsHadamard2 (H.submatrix rows cols)

def IsDephased (H : Mat6) : Prop :=
  (∀ j, H (Sum.inl 0) j = 1) ∧
  (∀ i, H i (Sum.inl 0) = 1)

def IsCubicRoot (z : ℂ) : Prop := z ^ 3 = 1

def HasNoninitialCubicRootRowAndColumn (H : Mat6) : Prop :=
  IsDephased H ∧
  (∃ i, i ≠ Sum.inl 0 ∧ ∀ j, IsCubicRoot (H i j)) ∧
  (∃ j, j ≠ Sum.inl 0 ∧ ∀ i, IsCubicRoot (H i j))

/-- The union of the two exceptional sectors used by the routing theorem. -/
def InKnownExceptionalSector
    (IsTao IsKarlsson : Mat6 → Prop) (H : Mat6) : Prop :=
  IsKarlsson H ∨ IsTao H

/-- The intrinsic implication needed by the block-swap argument. -/
def TwoByTwoKarlssonCriterion (IsKarlsson : Mat6 → Prop) : Prop :=
  ∀ H, IsHadamard H → HasHadamardTwoByTwo H → IsKarlsson H

end Hadamard6
