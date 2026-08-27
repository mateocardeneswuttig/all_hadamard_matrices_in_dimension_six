import Hadamard6.ConcreteClassification
import Hadamard6.H2KarlssonParametrization
import Hadamard6.KarlssonContainment
import Hadamard6.TaoAtlas

/-!
# Equivalence classes of order-six Hadamard matrices

This file states the concrete atlas theorem on the actual quotient by
Hadamard equivalence.  The predicates are lifted only after their invariance
has been proved, so they cannot depend on a chosen representative.
-/

namespace Hadamard6

/-- The concrete Tao orbit and intrinsic Karlsson sector are disjoint. -/
theorem isTaoOrbit_not_isKarlssonConcrete {H : Mat6}
    (hTao : IsTaoOrbit H) : ¬ IsKarlssonConcrete H := by
  rcases hTao with ⟨omega, homega, heq⟩
  intro hKarlsson
  have htwoTao : HasHadamardTwoByTwo (taoMatrix omega) :=
    (equivalent_hasHadamardTwoByTwo_iff heq).1 hKarlsson.2
  exact taoMatrix_not_hasHadamardTwoByTwo homega htwoTao

/-- The type of order-six Hadamard matrices before quotienting. -/
abbrev Had6 := {H : Mat6 // IsHadamard H}

def had6EquivalenceSetoid : Setoid Had6 where
  r H K := Equivalent H.1 K.1
  iseqv := ⟨
    (fun H ↦ equivalent_refl H.1),
    (fun h ↦ equivalent_symm h),
    (fun h₁ h₂ ↦ equivalent_trans h₁ h₂)⟩

/-- Equivalence classes of order-six complex Hadamard matrices. -/
abbrev HadamardClass6 := Quotient had6EquivalenceSetoid

def FiniteCornerAtlasClass : HadamardClass6 → Prop :=
  Quotient.lift
    (fun H : Had6 ↦ InFiniteCornerAtlas H.1)
    (by
      intro H K hHK
      exact propext (equivalent_inFiniteCornerAtlas_iff hHK))

def KarlssonClass : HadamardClass6 → Prop :=
  Quotient.lift
    (fun H : Had6 ↦ IsKarlssonConcrete H.1)
    (by
      intro H K hHK
      exact propext (equivalent_isKarlssonConcrete_iff hHK))

def TaoClass : HadamardClass6 → Prop :=
  Quotient.lift
    (fun H : Had6 ↦ IsTaoOrbit H.1)
    (by
      intro H K hHK
      exact propext (equivalent_isTaoOrbit_iff hHK))

def FiniteCornerAtlasClasses : Set HadamardClass6 :=
  {q | FiniteCornerAtlasClass q}
def KarlssonClasses : Set HadamardClass6 := {q | KarlssonClass q}
def TaoClasses : Set HadamardClass6 := {q | TaoClass q}

@[simp] theorem finiteCornerAtlasClass_mk (H : Had6) :
    FiniteCornerAtlasClass (Quotient.mk had6EquivalenceSetoid H) ↔
      InFiniteCornerAtlas H.1 :=
  Iff.rfl

@[simp] theorem karlssonClass_mk (H : Had6) :
    KarlssonClass (Quotient.mk had6EquivalenceSetoid H) ↔
      IsKarlssonConcrete H.1 :=
  Iff.rfl

@[simp] theorem taoClass_mk (H : Had6) :
    TaoClass (Quotient.mk had6EquivalenceSetoid H) ↔ IsTaoOrbit H.1 :=
  Iff.rfl

/-- Tao containment in the quotient atlas is unconditional. -/
theorem taoClasses_subset_finiteCornerAtlasClasses :
    TaoClasses ⊆ FiniteCornerAtlasClasses := by
  intro q hq
  induction q using Quotient.inductionOn with
  | _ H =>
      change IsTaoOrbit H.1 at hq
      change InFiniteCornerAtlas H.1
      exact isTaoOrbit_mem_finiteCornerAtlas hq

/-- Karlsson containment in the quotient atlas is proved internally. -/
theorem karlssonClasses_subset_finiteCornerAtlasClasses :
    KarlssonClasses ⊆ FiniteCornerAtlasClasses := by
  intro q hq
  induction q using Quotient.inductionOn with
  | _ H =>
      change IsKarlssonConcrete H.1 at hq
      change InFiniteCornerAtlas H.1
      exact hasHadamardTwoByTwo_mem_finiteCornerAtlas
        H.2 hq.2

/-- The named Tao and Karlsson loci are disjoint on equivalence classes. -/
theorem taoClasses_disjoint_karlssonClasses :
    Disjoint TaoClasses KarlssonClasses := by
  rw [Set.disjoint_left]
  intro q hTao hKarlsson
  induction q using Quotient.inductionOn with
  | _ H =>
      exact isTaoOrbit_not_isKarlssonConcrete hTao hKarlsson

noncomputable def standardTaoHad6 : Had6 :=
  ⟨taoMatrix standardOmega,
    taoMatrix_isHadamard standardOmega_isPrimitiveCubicPhase⟩

noncomputable def standardTaoClass : HadamardClass6 :=
  Quotient.mk had6EquivalenceSetoid standardTaoHad6

theorem standardTaoClass_mem_taoClasses :
    standardTaoClass ∈ TaoClasses := by
  change IsTaoOrbit (taoMatrix standardOmega)
  exact ⟨standardOmega, standardOmega_isPrimitiveCubicPhase,
    equivalent_refl _⟩

theorem standardTaoClass_mem_finiteCornerAtlasClasses :
    standardTaoClass ∈ FiniteCornerAtlasClasses :=
  taoClasses_subset_finiteCornerAtlasClasses standardTaoClass_mem_taoClasses

theorem standardTaoClass_not_mem_karlssonClasses :
    standardTaoClass ∉ KarlssonClasses := by
  change ¬ IsKarlssonConcrete (taoMatrix standardOmega)
  exact isTaoOrbit_not_isKarlssonConcrete
    ⟨standardOmega, standardOmega_isPrimitiveCubicPhase,
      equivalent_refl _⟩

/-- Quotient-level proper containment.  This formulation avoids any
notation-dependent definition of strict set inclusion. -/
theorem karlssonClasses_properly_contained_in_finiteCornerAtlasClasses :
    KarlssonClasses ⊆ FiniteCornerAtlasClasses ∧
      ¬ FiniteCornerAtlasClasses ⊆ KarlssonClasses := by
  constructor
  · exact karlssonClasses_subset_finiteCornerAtlasClasses
  · intro hreverse
    exact standardTaoClass_not_mem_karlssonClasses
      (hreverse standardTaoClass_mem_finiteCornerAtlasClasses)

end Hadamard6
