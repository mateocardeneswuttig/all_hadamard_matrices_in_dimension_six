# Public Lean theorem audit

## Human-readable proof spine

`Hadamard6/PaperTheorem.lean` is intentionally short. Its principal proof now
uses the same contradiction structure as the manuscript:

```text
assume hfailed : not HasFiniteCorner H
paper_failed_corner_search_forces_karlsson_or_tao hH hfailed
  : IsKarlssonConcrete H ∨ IsTaoOrbit H

Karlsson branch -> paper_karlsson_has_finite_corner -> contradiction
Tao branch      -> paper_tao_has_finite_corner       -> contradiction
```

The result is `paper_finite_corner_theorem`.  Atlas membership and equality
are derived afterwards.  This ordering prevents the output definition from
doing any logical work in the witness theorem.

## Concrete predicates

- `IsKarlssonConcrete H` means exactly that `H` is Hadamard and contains a
  `2 x 2` Hadamard submatrix.  Karlsson's published theorem identifies this
  intrinsic locus with his complete three-parameter family.
- `IsTaoOrbit H` means that `H` is standard-equivalent to the displayed Tao
  matrix for a primitive cubic phase.
- `InFiniteCornerAtlas H` unfolds to a four-phase dephased seed, two finite
  nonempty normalized invertible candidate fibres, an actual candidate pair,
  the forced block and its entrywise-unit test, and equivalence to the
  completed matrix.

None is an opaque family placeholder.

## Exact proof flow

Lean reduces the cubic-root row-and-column branch to the simultaneous Fourier
normal form and checks its finite cubic phase table explicitly, obtaining
exactly Tao or `IsKarlssonConcrete`.

For the Karlsson branch, Lean intrinsically normalizes an `H₂`-reducible
Hadamard into canonical raw coordinates or five explicit exceptional
residues. It proves the reciprocal orientation and selection of nonzero
`M₊`, verifies the regular raw finite-corner certificate, and proves exact
equivalences carrying every exceptional residue to an affine-Fourier seam.
The resulting theorem `karlssonRawOrSeamCoverage_proved` is consumed
internally; it is not an argument of a public theorem.

The theorem `paper_nonexceptional_completed_dilation_recovery` excludes Karlsson and
Tao in its hypotheses, so the routing disjunction closes it without the
Karlsson finite-corner theorem. It deliberately does not call this predicate
`G_6^(4)`: the manuscript's separate construction-level output-identification
proposition is what converts completed-output recovery into the three-sector
conjecture.

## Kernel and source audit

The public file prints axiom reports for nine endpoints.  A passing build must
show only:

```text
propext, Classical.choice, Quot.sound
```

The source audit separately rejects `sorry`, `admit`, project-defined
`axiom`/`constant`, source-level `opaque`/`unsafe` declarations, and unchecked
native-decision shortcuts. The thousands figure shown by Lake is its
scheduler count including Mathlib, not a count of assumptions or bespoke
classification lemmas.

The public theorem signatures contain no literature-facing theorem
parameters. Accordingly, the clean source and axiom reports audit an
unconditional Lean derivation of the paper-facing finite-corner
classification from the concrete definitions in this repository.
