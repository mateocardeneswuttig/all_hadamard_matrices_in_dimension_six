import Hadamard6.FourierCubicCasesPOne
import Hadamard6.FourierCubicCasesPOmega
import Hadamard6.FourierCubicCasesPOmegaSq

/-!
# Classification of the cubic simultaneous-Fourier chart

The public theorem below is the specialized replacement for the published
cubic-root row/column criterion on the exact branch reached by the
classification proof.
-/

namespace Hadamard6

noncomputable section

/-- A physical forced Fourier normal form with four cubic gauge phases is
either Tao-equivalent or contains a Hadamard `2 x 2` submatrix. -/
theorem cubicFourierNormalForm_classified
    {omega p q r s : ℂ}
    (homega : IsPrimitiveCubicPhase omega)
    (hp : IsCubicRoot p) (hq : IsCubicRoot q)
    (hr : IsCubicRoot r) (hs : IsCubicRoot s)
    (hH : IsHadamard
      (fourierNormalForm omega p q r s
        (fourierForcedD omega p q r s))) :
    IsTaoOrbit
        (fourierNormalForm omega p q r s
          (fourierForcedD omega p q r s)) ∨
      HasHadamardTwoByTwo
        (fourierNormalForm omega p q r s
          (fourierForcedD omega p q r s)) := by
  rcases cubicRoot_eq_one_or_primitive_or_sq homega hp with hp0 | hp1 | hp2
  · subst p
    exact cubicFourierNormalForm_classified_p_one homega hq hr hs hH
  · subst p
    exact cubicFourierNormalForm_classified_p_omega homega hq hr hs hH
  · subst p
    exact cubicFourierNormalForm_classified_p_omega_sq homega hq hr hs hH

end

end Hadamard6

