import Hadamard6.FourierNormalizationClassification
import Hadamard6.HadamardQuotient

/-!
# Paper-facing classification theorem

This is the audit entry point for the manuscript's proof:

1. failure of the 400-corner search forces the intrinsic Karlsson locus or
   the Tao orbit;
2. the Karlsson and Tao propositions give finite corners on those loci;
3. contradiction proves the universal finite-corner theorem;
4. completeness and soundness give the retained-output equality, first on
   matrices and then on equivalence classes.

The cubic Fourier branch and the intrinsic `H₂` normalization are proved
internally.  Lean extracts the regular Karlsson coordinates, identifies all
residual affine-Fourier seams, proves the regular Karlsson, seam, and Tao
finite-corner certificates, and then checks routing, soundness, and both
class inclusions.  Atlas membership and class equality are consequences of
witness existence, not definitions used to obtain it.
-/

namespace Hadamard6

/-- Constructive routing lemma underlying the paper's failed-search
proposition. Its simultaneous-Fourier branch is classified internally;
Karlsson finite-corner coverage is not used here. -/
private theorem paper_corner_search_routing
    {H : Mat6} (hH : IsHadamard H) :
    HasFiniteCorner H ∨ IsKarlssonConcrete H ∨ IsTaoOrbit H := by
  rcases exceptional_or_finiteCornerAtlas H hH with
      (hKarlsson | hTao) | hfinite
  · exact Or.inr (Or.inl hKarlsson)
  · exact Or.inr (Or.inr hTao)
  · exact Or.inl (inFiniteCornerAtlas_hasFiniteCorner hfinite)

/-- Paper Proposition "absence of every finite-corner witness forces
Karlsson or Tao", in the same implication form as the manuscript. -/
theorem paper_failed_corner_search_forces_karlsson_or_tao
    {H : Mat6} (hH : IsHadamard H)
    (hfailed : ¬ HasFiniteCorner H) :
    IsKarlssonConcrete H ∨ IsTaoOrbit H := by
  rcases paper_corner_search_routing hH with
      hfinite | hKarlsson | hTao
  · exact False.elim (hfailed hfinite)
  · exact Or.inl hKarlsson
  · exact Or.inr hTao

/-- Paper Proposition "finite-corner witnesses for the Karlsson locus".
Both the intrinsic raw-or-seam reduction and the finite-corner certificates
are internal. -/
theorem paper_karlsson_has_finite_corner
    {H : Mat6} (hKarlsson : IsKarlssonConcrete H) : HasFiniteCorner H :=
  inFiniteCornerAtlas_hasFiniteCorner
    (hasHadamardTwoByTwo_mem_finiteCornerAtlas
      hKarlsson.1 hKarlsson.2)

/-- Paper Proposition "a finite-corner witness for Tao", verified internally. -/
theorem paper_tao_has_finite_corner
    {H : Mat6} (hTao : IsTaoOrbit H) : HasFiniteCorner H :=
  inFiniteCornerAtlas_hasFiniteCorner
    (isTaoOrbit_mem_finiteCornerAtlas hTao)

/-- Main theorem: the manuscript's contradiction argument verbatim at the
predicate level. -/
theorem paper_finite_corner_theorem
    {H : Mat6} (hH : IsHadamard H) : HasFiniteCorner H := by
  by_contra hfailed
  rcases paper_failed_corner_search_forces_karlsson_or_tao
      hH hfailed with hKarlsson | hTao
  · exact hfailed (paper_karlsson_has_finite_corner hKarlsson)
  · exact hfailed (paper_tao_has_finite_corner hTao)

/-- Nonexceptional recovery by our completed output.  The manuscript's
separate comparison with Construction 3.1 is not formalized here. -/
theorem paper_nonexceptional_completed_dilation_recovery
    {H : Mat6} (hH : IsHadamard H)
    (hnotKarlsson : ¬ IsKarlssonConcrete H)
    (hnotTao : ¬ IsTaoOrbit H) : InFiniteCornerAtlas H := by
  rcases paper_corner_search_routing hH with
      hfinite | hKarlsson | hTao
  · exact finiteCorner_mem_finiteCornerAtlas hfinite
  · exact False.elim (hnotKarlsson hKarlsson)
  · exact False.elim (hnotTao hTao)

/-- Algorithmic consequence: every Hadamard class occurs in the total
retained finite-corner output. -/
theorem paper_finite_corner_completeness
    {H : Mat6} (hH : IsHadamard H) :
    InFiniteCornerAtlas H :=
  finiteCorner_mem_finiteCornerAtlas
    (paper_finite_corner_theorem hH)

/-- Soundness is unconditional: every retained output is Hadamard. -/
theorem paper_finite_corner_soundness {H : Mat6}
    (hH : InFiniteCornerAtlas H) : IsHadamard H :=
  inFiniteCornerAtlas_isHadamard hH

/-- Two-sided class equality, stated only after witness existence. -/
theorem paper_total_output_corollary
    (H : Mat6) :
    IsHadamard H ↔ InFiniteCornerAtlas H := by
  constructor
  · exact paper_finite_corner_completeness
  · exact paper_finite_corner_soundness

/-- Equivalence-class form of the classification corollary.  The quotient
already contains only Hadamard matrices, so equality with `Set.univ` is
precisely the paper's `H_6 = A_6^fc`. -/
theorem paper_classification_corollary :
    FiniteCornerAtlasClasses = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ H =>
      change InFiniteCornerAtlas H.1
      exact paper_finite_corner_completeness H.2

/- The formerly external Karlsson coverage statement is now a theorem. -/
#print axioms karlssonRawOrSeamCoverage_proved

#print axioms paper_failed_corner_search_forces_karlsson_or_tao
#print axioms paper_karlsson_has_finite_corner
#print axioms paper_tao_has_finite_corner
#print axioms paper_finite_corner_theorem
#print axioms paper_nonexceptional_completed_dilation_recovery
#print axioms paper_finite_corner_completeness
#print axioms paper_finite_corner_soundness
#print axioms paper_total_output_corollary
#print axioms paper_classification_corollary

end Hadamard6
