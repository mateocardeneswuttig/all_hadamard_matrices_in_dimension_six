import Hadamard6.PaperTheorem

/-!
# Order-six classification audit

The library root intentionally exposes one paper-facing module. Its
transitive imports contain the detailed algebra and exact certificates, but a
reader auditing the classification should begin with
`Hadamard6/PaperTheorem.lean`. Its principal theorem now uses the same
failed-search contradiction as the manuscript. Both exceptional branches are
proved internally: the cubic Fourier normal form is classified into Tao or
the intrinsic `H₂` sector, and every intrinsic `H₂` matrix is reduced to a
regular Karlsson presentation or an explicitly verified affine-Fourier seam.
-/
