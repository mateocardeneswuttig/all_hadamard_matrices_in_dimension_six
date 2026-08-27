# What Lean assumes and what it proves

The public endpoint is `Hadamard6/PaperTheorem.lean`. Its classification
theorems take no literature-facing theorem argument.

## Assumes

No project-specific mathematical proposition. The public theorems assume only
their stated object-level data, for example a matrix `H` and a proof
`IsHadamard H`.

## Proves internally

Lean proves:

- Hadamard equivalence and invariance of every public predicate;
- the singular-corner reduction and normalized fixed-Gram fibre trichotomy;
- complementary-block sign reversal, corner routing, and Fourier-block
  closure;
- the simultaneous cubic Fourier normal form is exactly classified into the
  Tao orbit or the intrinsic `H₂` sector by an explicit finite table;
- the explicit Tao orbit and its finite-corner witness;
- exact finite-corner certificates on the regular Karlsson chart;
- exact finite-corner certificates for every affine-Fourier seam, including
  transpose transfer;
- intrinsic normalization of every `H₂`-reducible matrix into regular raw
  coordinates or five explicit exceptional residues, and exact equivalences
  carrying all exceptional residues to an affine-Fourier seam;
- forced completion and retained-output Hadamard soundness;
- `HasFiniteCorner H ↔ InFiniteCornerAtlas H`;
- the universal finite-corner theorem; and
- matrix-level and equivalence-class-level two-sided classification
  equalities.

The finite-corner definition matches the manuscript: it requires finite,
nonempty, invertible horizontal and vertical candidate fibres containing the
actual adjacent blocks. It does not require the seed block `E` to be
invertible; the completion formula inverts the adjacent block `B`.

The longer `H2...` modules derive the intrinsic normalization and canonical
raw coordinates. `IntrinsicKarlssonSeam.lean` combines those results with the
explicit exceptional-seam equivalences to prove
`karlssonRawOrSeamCoverage_proved`; `KarlssonContainment.lean` then consumes
that theorem rather than accepting coverage as an argument.

## Does not prove

Lean does not formalize:

- the construction-level comparison with Szöllősi's Construction 3.1;
- the generic quadratic--cubic reconstruction geometry;
- nonsplitting of the product cover;
- the physical seed-domain theorem;
- global product-regular reach; or
- the illustrative ramification seed.

The retained post-classification calculations are instead supplied in
`certificates/`, with a SHA-256 manifest and a one-command verifier. They are
not represented as Lean theorems.

## Trust statement

The project contains no `sorry`, `admit`, project-defined `axiom` or
`constant`, source-level `opaque` or `unsafe` declaration, or unchecked
`native_decide`. `#print axioms` on the nine public endpoints reports only
the ordinary Lean/Mathlib foundations `propext`, `Classical.choice`, and
`Quot.sound`. No additional mathematical axiom or theorem parameter occurs in
the paper-facing classification signatures.
