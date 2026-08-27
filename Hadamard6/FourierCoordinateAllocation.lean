import Hadamard6.CubicRoots
import Hadamard6.Blocks

/-!
# The finite allocation in the Fourier-block chart

This file isolates the elementary four-case argument after simultaneous
Fourier normalization and the cyclic-convolution calculation.  The chart
construction itself is represented by `FourierChartReduction`; everything
after its two product equations is proved here.
-/

namespace Hadamard6

theorem cubic_mul_cancel_left {a b : ℂ}
    (ha : IsCubicRoot a) (hab : IsCubicRoot (a * b)) :
    IsCubicRoot b := by
  calc
    b ^ 3 = a ^ 3 * b ^ 3 := by rw [ha]; ring
    _ = (a * b) ^ 3 := by ring
    _ = 1 := hab

theorem cubic_star_iff {z : ℂ} :
    IsCubicRoot (star z) ↔ IsCubicRoot z := by
  unfold IsCubicRoot
  constructor <;> intro h
  · have hs := congrArg star h
    simpa [map_pow] using hs
  · have hs := congrArg star h
    simpa [map_pow] using hs

theorem cubic_square {z : ℂ} (hz : IsCubicRoot z) :
    IsCubicRoot (z ^ 2) := by
  rw [IsCubicRoot, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num,
    pow_mul, hz]
  norm_num

theorem A₁_zero_parameters_cubic
    {ω p q A₁ : ℂ}
    (hωu : Complex.normSq ω = 1) (hω3 : IsCubicRoot ω)
    (hp : Complex.normSq p = 1) (hq : Complex.normSq q = 1)
    (hA : A₁ = 3 * (q + ω * star p + ω ^ 2 * p * star q))
    (hA0 : A₁ = 0) : IsCubicRoot p ∧ IsCubicRoot q := by
  have hs : q + ω * star p + ω ^ 2 * p * star q = 0 := by
    rw [hA] at hA0
    apply mul_eq_zero.mp hA0 |>.resolve_left
    norm_num
  have hx : Complex.normSq q = 1 := hq
  have hy : Complex.normSq (ω * star p) = 1 := by
    simp [Complex.normSq_mul, Complex.normSq_conj, hωu, hp]
  have hz : Complex.normSq (ω ^ 2 * p * star q) = 1 := by
    simp [pow_two, Complex.normSq_mul, Complex.normSq_conj,
      hωu, hp, hq]
  have hprod : q * (ω * star p) * (ω ^ 2 * p * star q) = 1 := by
    have hp' : star p * p = 1 := star_mul_self_of_normSq_one hp
    have hq' : star q * q = 1 := star_mul_self_of_normSq_one hq
    rw [show q * (ω * star p) * (ω ^ 2 * p * star q) =
      ω ^ 3 * (star p * p) * (star q * q) by ring,
      hω3, hp', hq']
    norm_num
  rcases unit_sum_zero_product_one_are_cubic hx hy hz hs hprod with
    ⟨hq3, hyp3, hz3⟩
  have hsp : IsCubicRoot (star p) :=
    cubic_mul_cancel_left hω3 hyp3
  exact ⟨cubic_star_iff.mp hsp, hq3⟩

theorem A₂_zero_parameters_cubic
    {ω p q A₂ : ℂ}
    (hωu : Complex.normSq ω = 1) (hω3 : IsCubicRoot ω)
    (hp : Complex.normSq p = 1) (hq : Complex.normSq q = 1)
    (hA : A₂ = 3 * (p + ω * q * star p + ω ^ 2 * star q))
    (hA0 : A₂ = 0) : IsCubicRoot p ∧ IsCubicRoot q := by
  have hs : p + ω * q * star p + ω ^ 2 * star q = 0 := by
    rw [hA] at hA0
    apply mul_eq_zero.mp hA0 |>.resolve_left
    norm_num
  have hx : Complex.normSq p = 1 := hp
  have hy : Complex.normSq (ω * q * star p) = 1 := by
    simp [Complex.normSq_mul, Complex.normSq_conj, hωu, hp, hq]
  have hz : Complex.normSq (ω ^ 2 * star q) = 1 := by
    simp [pow_two, Complex.normSq_mul, Complex.normSq_conj,
      hωu, hq]
  have hprod : p * (ω * q * star p) * (ω ^ 2 * star q) = 1 := by
    have hp' : star p * p = 1 := star_mul_self_of_normSq_one hp
    have hq' : star q * q = 1 := star_mul_self_of_normSq_one hq
    rw [show p * (ω * q * star p) * (ω ^ 2 * star q) =
      ω ^ 3 * (star p * p) * (star q * q) by ring,
      hω3, hp', hq']
    norm_num
  rcases unit_sum_zero_product_one_are_cubic hx hy hz hs hprod with
    ⟨hp3, hy3, hz3⟩
  have hω2 : IsCubicRoot (ω ^ 2) := cubic_square hω3
  have hsq : IsCubicRoot (star q) :=
    cubic_mul_cancel_left hω2 hz3
  exact ⟨hp3, cubic_star_iff.mp hsq⟩

theorem α₁_zero_parameters_cubic
    {ω r s α₁ : ℂ}
    (hωu : Complex.normSq ω = 1) (hω3 : IsCubicRoot ω)
    (hr : Complex.normSq r = 1) (hsu : Complex.normSq s = 1)
    (hα : α₁ = star r + ω * r * star s + ω ^ 2 * s)
    (hα0 : α₁ = 0) : IsCubicRoot r ∧ IsCubicRoot s := by
  have hx : Complex.normSq (star r) = 1 := by
    simp [Complex.normSq_conj, hr]
  have hy : Complex.normSq (ω * r * star s) = 1 := by
    simp [Complex.normSq_mul, Complex.normSq_conj, hωu, hr, hsu]
  have hz : Complex.normSq (ω ^ 2 * s) = 1 := by
    simp [pow_two, Complex.normSq_mul, hωu, hsu]
  have hsum : star r + ω * r * star s + ω ^ 2 * s = 0 := hα ▸ hα0
  have hprod : star r * (ω * r * star s) * (ω ^ 2 * s) = 1 := by
    rw [show star r * (ω * r * star s) * (ω ^ 2 * s) =
      ω ^ 3 * (star r * r) * (star s * s) by ring,
      hω3, star_mul_self_of_normSq_one hr,
      star_mul_self_of_normSq_one hsu]
    norm_num
  rcases unit_sum_zero_product_one_are_cubic hx hy hz hsum hprod with
    ⟨hsr, hy3, hω2s⟩
  exact ⟨cubic_star_iff.mp hsr,
    cubic_mul_cancel_left (cubic_square hω3) hω2s⟩

theorem α₂_zero_parameters_cubic
    {ω r s α₂ : ℂ}
    (hωu : Complex.normSq ω = 1) (hω3 : IsCubicRoot ω)
    (hr : Complex.normSq r = 1) (hsu : Complex.normSq s = 1)
    (hα : α₂ = star r + ω ^ 2 * r * star s + ω * s)
    (hα0 : α₂ = 0) : IsCubicRoot r ∧ IsCubicRoot s := by
  have hx : Complex.normSq (star r) = 1 := by
    simp [Complex.normSq_conj, hr]
  have hy : Complex.normSq (ω ^ 2 * r * star s) = 1 := by
    simp [pow_two, Complex.normSq_mul, Complex.normSq_conj,
      hωu, hr, hsu]
  have hz : Complex.normSq (ω * s) = 1 := by
    simp [Complex.normSq_mul, hωu, hsu]
  have hsum : star r + ω ^ 2 * r * star s + ω * s = 0 := hα ▸ hα0
  have hprod : star r * (ω ^ 2 * r * star s) * (ω * s) = 1 := by
    rw [show star r * (ω ^ 2 * r * star s) * (ω * s) =
      ω ^ 3 * (star r * r) * (star s * s) by ring,
      hω3, star_mul_self_of_normSq_one hr,
      star_mul_self_of_normSq_one hsu]
    norm_num
  rcases unit_sum_zero_product_one_are_cubic hx hy hz hsum hprod with
    ⟨hsr, hy3, hωs⟩
  exact ⟨cubic_star_iff.mp hsr, cubic_mul_cancel_left hω3 hωs⟩

/-- Exact output of the simultaneous Fourier normal form and cyclic
convolution calculation.  This is the remaining chart-construction input;
the allocation of its two product equations is proved below. -/
structure FourierChart (H : Mat6) where
  K : Mat6
  hK : IsHadamard K
  equivalent : Equivalent H K
  ω : ℂ
  p : ℂ
  q : ℂ
  r : ℂ
  s : ℂ
  A₁ : ℂ
  A₂ : ℂ
  α₁ : ℂ
  α₂ : ℂ
  ω_unit : Complex.normSq ω = 1
  ω_cubic : IsCubicRoot ω
  p_unit : Complex.normSq p = 1
  q_unit : Complex.normSq q = 1
  r_unit : Complex.normSq r = 1
  s_unit : Complex.normSq s = 1
  A₁_formula : A₁ = 3 * (q + ω * star p + ω ^ 2 * p * star q)
  A₂_formula : A₂ = 3 * (p + ω * q * star p + ω ^ 2 * star q)
  α₁_formula : α₁ = star r + ω * r * star s + ω ^ 2 * s
  α₂_formula : α₂ = star r + ω ^ 2 * r * star s + ω * s
  factor₁ : α₁ * A₁ = 0
  factor₂ : α₂ * A₂ = 0
  twoByTwo_of_A_zero : A₁ = 0 → A₂ = 0 → HasHadamardTwoByTwo H
  twoByTwo_of_α_zero : α₁ = 0 → α₂ = 0 → HasHadamardTwoByTwo H
  cubic_of_parameters :
    IsCubicRoot p → IsCubicRoot q → IsCubicRoot r → IsCubicRoot s →
      HasNoninitialCubicRootRowAndColumn K

def FourierChartReduction : Prop :=
  ∀ H, IsHadamard H → AllFourBlocksHadamard H → Nonempty (FourierChart H)

end Hadamard6
