# Paper-to-Lean proof map

The authoritative endpoint is `Hadamard6/PaperTheorem.lean`.  Read its
theorems from top to bottom; they deliberately match the manuscript order.

| Manuscript statement | Manuscript label | Lean theorem | Status in Lean |
|---|---|---|---|
| Absence of every finite-corner witness forces Karlsson or Tao | `thm:finitecornerintro` (typeset as a proposition) | `paper_failed_corner_search_forces_karlsson_or_tao` | proved internally |
| Every Karlsson class has a finite corner | `prop:karlsson-finite-corner` | `paper_karlsson_has_finite_corner` | proved internally from intrinsic `H₂` normalization and exact seam equivalences |
| Tao has a finite corner | `prop:tao-finite-corner` | `paper_tao_has_finite_corner` | proved internally |
| Every order-six Hadamard matrix has a finite corner | `thm:classification` | `paper_finite_corner_theorem` | proved internally |
| Non-Tao, non-Karlsson completed-output recovery | intermediate consequence used before `prop:historical-output-identification` | `paper_nonexceptional_completed_dilation_recovery` | proved internally |
| Every Hadamard lies in the retained output | proof of `cor:atlas-classification` | `paper_finite_corner_completeness` | proved internally |
| Every retained output is Hadamard | `prop:algorithmvalid` | `paper_finite_corner_soundness` | proved internally |
| Matrix-level two-sided equality | `cor:atlas-classification` before quotienting | `paper_total_output_corollary` | proved internally |
| Equality on equivalence classes | `cor:atlas-classification` | `paper_classification_corollary` | proved internally |

The manuscript's source key for the failed-search proposition begins with
`thm:` although the statement is typeset as a proposition. The table records
the literal key so references can be audited mechanically.

## Internal dependency layers

| Mathematical layer | Main Lean files |
|---|---|
| Definitions, equivalence, and quotient | `Basic.lean`, `PhaseEquivalence.lean`, `HadamardQuotient.lean` |
| Finite-corner predicate and completion soundness | `FiniteDilation.lean`, `Blocks.lean`, `BlockCompletion.lean` |
| Singular-corner reduction | `VanishingMinorReduction.lean` |
| Fixed-Gram fibre trichotomy | `CandidateFibre.lean`, `InfiniteFibre*.lean`, `Dependent*.lean` |
| Complementary-block routing | `BlockSwap*.lean`, `Classification.lean` |
| Fourier-block closure and cubic classification | `Fourier*.lean`, `SimultaneousFourierNormalization.lean`, `FourierCubic*.lean`, `FourierNormalizationClassification.lean` |
| Tao witness | `TaoOrbit.lean`, `TaoAtlas.lean` |
| Intrinsic Karlsson normalization and coordinate extraction | `H2CanonicalForm.lean`, `H2BlockNormalization.lean`, `H2DegenerateNormalization.lean`, `H2KarlssonParametrization.lean` |
| Karlsson raw coordinates and reciprocal orientation | `KarlssonGlobalModel.lean`, `KarlssonChartBoundary.lean` |
| Karlsson regular chart | `KarlssonMixedBlocks.lean` and its certificate imports |
| Karlsson affine-Fourier seam | `KarlssonFourierSeam.lean`, `FourierSeamCertificate*.lean`, `H2ExceptionalSeam*.lean`, `IntrinsicKarlssonSeam.lean` |
| Public recombination | `PaperTheorem.lean` |

The two generated arithmetic modules are deliberately terminal backends, not
alternative theorem spines. `KarlssonResidualCertificate.lean` certifies the
compact residual by exact Bernstein identities, while
`KarlssonWitnessResultants.lean` certifies four explicit reciprocal
resultants. Their mathematical routing is visible in the much shorter
consumer modules; their size records exact coefficients, not additional
assumptions or classification cases.

No Lean predicate named after (G_6^{(4)}) denotes the total atlas.  The
formal vocabulary uses `InFiniteCornerAtlas` throughout.  The paper's
separate construction-level identification with the nonexceptional output of Construction 3.1 is not
encoded as a definitional alias.

The modules beginning `H2...` derive Karlsson's intrinsic normalization and
canonical raw chart.  They reduce the final exceptional cores to explicit
finite cases; `H2ExceptionalSeam*.lean` identifies those cases with the
affine-Fourier seam, and `IntrinsicKarlssonSeam.lean` assembles the resulting
unconditional raw-or-seam coverage theorem.

## Deliberate formal boundary

The Lean endpoint proves the main finite-corner theorem and the equality
`H_6 = A_6^fc`. It does not currently prove the manuscript's separate
construction-level proposition identifying the nonexceptional part of
`A_6^fc` with Szöllősi's Construction 3.1 output. Consequently it does not
export the three-sector `G_6^(4) dot-union K_6^(3) dot-union T_6` corollary.
That omission is explicit rather than encoded by redefining `G_6^(4)`.
