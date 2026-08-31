# Paper claim and verification audit

This file records the proof boundary after the August 2026 manuscript audit.
It is intentionally organized by mathematical claim rather than by the
history of the exploratory computation.

| Paper claim | Status | Verification source |
|---|---|---|
| Complete finite-corner classification (Theorem 6) | Exact and unconditional | Printed proof and `Hadamard6/PaperTheorem.lean` |
| Soundness and exact retained output | Exact | Printed direct-completion proof and Lean |
| Karlsson finite-corner coverage | Exact | Printed reduction; generated resultant and Bernstein identities are kernel checked in Lean |
| Tao finite-corner witness | Exact | Printed calculation and Lean |
| Szöllősi sector identification and Conjecture 4.2 | Exact mathematical consequence, not Lean formalized | Printed fixed-corner comparison plus the classification theorem |
| Product quadratic/cubic reconstruction | Exact | Printed identities and `generic_cover/product_cubic_*.py` |
| Generic cover is nonsplit | Exact | Printed square-free specialization and `generic_cover/product_discriminant_check.py` |
| Horizontal and vertical covers have the same branch function | Exact | `generic_cover/horizontal_vertical_cover_check.py` |
| Complement positivity, including `omega_n = 0` | Exact | Printed proof and `generic_cover/positivity_lemma_reduction.py` |
| Generic lower-block minus matching | Exact | Printed irreducibility/dominance proof; `generic_cover/exact_lower_block_specialization.py` verifies nonempty regular localization and excludes the plus matching |
| Regular seed-domain theorem (Theorem 21) | Exact | Printed proof plus the five generic-cover certificates above; the dominance step cites Bondal--Zhdanovskiy and semialgebraic Hardt triviality |
| Exact product-regular reach (Theorem 22) | Exact | The printed `100 > 80` proof and all six files in `product_escape/` cover classes outside Karlsson and Tao; `product_exceptional/` proves `K_6^(3) \ P_6 = {[H_x]}` and excludes Tao and `H_x` in all `14,400` frames |
| Product-exceptional Karlsson singleton | Exact, using the published Matszangosz--Szollosi routing theorem | Printed sector reduction and `product_exceptional/karlsson_product_regular_coverage/karlsson_product_exceptional_theorem_check.py` |
| Tao is product exceptional | Exact finite enumeration | `product_exceptional/tao_product_exceptional_check.py` |
| Representative ramification seed and table | Rigorous exact/interval diagnostic, explicitly not a theorem about a neighborhood | `ramification/ramification_seed_certificate.py` |
| Section IV figure | Numerical illustration only | `figure/` sources, component data, component PDFs, and final vector asset |

## Lean boundary

Lean is used only for the classification. Its public endpoint has no
literature-facing theorem parameter. The cubic Fourier branch is classified
internally by an explicit finite proof. The `H₂` branch is normalized
intrinsically into regular Karlsson coordinates or explicit exceptional
residues; exact equivalences identify all residues with the affine-Fourier
seam, and the regular and seam finite-corner certificates are checked in Lean.

The post-classification product geometry is deliberately absent from the Lean
dependency graph. It is supported by the smaller exact and interval
certificates in this directory.

## Claims omitted to minimize certification

The audit omits the following unnecessary assertions from the manuscript and
its Supplemental Material:

- framed Karlsson noncontainment and its obsolete unprinted
  degree-five/degree-eight factorization;
- the `13,632`-frame and `720`-ramified-frame numerical census at the example
  seed.

Neither is needed for the classification, Szöllősi's conjecture, the regular
seed-domain theorem, or the exact product-regular reach theorem.

## No frozen solver output

Every retained script reconstructs its polynomial or finite enumeration and
checks the claimed result. No manuscript theorem relies on an unverified
solver transcript, cached Gröbner basis, or unprinted factorization.
