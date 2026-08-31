# A complete classification of the complex Hadamard matrices of order six

This repository contains the Lean 4 audit trail for the paper's classification of 
order-six complex Hadamard matrices.  It formalizes the finite-corner
argument, its Karlsson and Tao branches, completion soundness, and the final
two-sided equality on equivalence classes.

For a first reading, open [`Hadamard6/PaperTheorem.lean`](Hadamard6/PaperTheorem.lean), 
which follows the manuscript's logical order:

```text
Hadamard H
  -> if no finite corner, intrinsic Karlsson or Tao      (routing)
  -> both exceptional sectors have a finite corner      (close branches)
  -> H belongs to the retained finite-dilation output   (completeness)
retained finite-dilation output -> Hadamard              (soundness)
  -> equality of equivalence classes                    (classification)
```

## Quick start

### 1. Install the prerequisites

You need Git, Python 3, and **Elan**, the Lean version manager.  Elan reads
this repository's [`lean-toolchain`](lean-toolchain) file and installs the
exact Lean release automatically; do not install a different Lean version by
hand.

On macOS or Linux:

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
```

On Windows, in PowerShell:

```powershell
curl -O --location https://elan.lean-lang.org/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
del elan-init.ps1
```

If Git is not already installed, install it before continuing.  On macOS,
`xcode-select --install` supplies Git and the command-line build tools.  For
interactive reading, VS Code with the official **Lean 4** extension by
`leanprover` is recommended but is not required to verify the project.

See the [official Lean installation guide](https://lean-lang.org/install/manual/)
or the [official Elan repository](https://github.com/leanprover/elan) for
platform-specific help.

### 2. Clone the project

```sh
git clone https://github.com/mateocardeneswuttig/all_hadamard_matrices_in_dimension_six.git
cd all_hadamard_matrices_in_dimension_six
```

### 3. Download the pinned dependencies

The repository pins both Lean and Mathlib.  The following optional command
downloads Mathlib's precompiled cache and can save substantial time:

```sh
lake exe cache get
```

The first invocation may itself compile the small cache utility.  If the
cache is unavailable, `lake build` remains correct but may compile much more
of Mathlib locally.

### 4. Build the proofs

To compile the public theorem and everything on which it depends:

```sh
lake build Hadamard6.PaperTheorem
```

To build the library's default target:

```sh
lake build
```

The default target intentionally imports only the paper-facing theorem spine,
so both commands verify the classification audit rather than unrelated
experimental work. A fresh full build can take several minutes; a few exact
symbolic certificate modules dominate the running time. Lean may also print
informational tactic suggestions and standard-foundation axiom reports. These
are not proof gaps.

### 5. Run the trust-boundary audit

On macOS or Linux:

```sh
python3 audit_public_theorem.py
```

On Windows:

```powershell
py -3 audit_public_theorem.py
```

A successful run ends with messages of the following form (the module count
may increase as the proof is factored into smaller files):

```text
PASS Lean source contains no sorry, admit, project axiom/constant, opaque/unsafe declaration, or native_decide
PASS all ... Hadamard6 modules are reachable from Hadamard6.lean
PASS nine paper-facing axiom reports use only propext, Classical.choice, and Quot.sound
ALL PUBLIC LEAN SOURCE AND AXIOM CHECKS PASSED
```

The same build and audit run automatically in GitHub Actions.

## What is proved, and what is assumed

The public classification theorem is unconditional: it takes a matrix and a
proof that the matrix is Hadamard, but no project-specific mathematical
hypothesis. In particular, Lean proves internally:

- Hadamard equivalence and invariance of the public predicates;
- the singular-corner reduction and fixed-Gram fibre trichotomy;
- complementary-block routing and simultaneous Fourier normalization;
- the explicit finite classification of the simultaneous cubic Fourier
  normal form into the Tao orbit or the intrinsic `H₂` sector;
- the exact Tao orbit and its finite-corner witness;
- intrinsic normalization of every `H₂`-reducible matrix into regular raw
  Karlsson coordinates or five explicit exceptional residues;
- finite-corner certificates for the regular Karlsson chart and every
  affine-Fourier seam;
- exact equivalences sending all five exceptional `H₂` residues to the
  affine-Fourier seam;
- forced completion and retained-output soundness;
- `HasFiniteCorner H <-> InFiniteCornerAtlas H`; and
- matrix-level and quotient-level two-sided classification equalities.

The proof does not import Karlsson's parametrization as an assumption and does
not formalize that historical parametrization in its entirety. It instead
proves exactly the intrinsic normalization, regular-coordinate, and seam
identities needed by the classification. Lean does not formalize the paper's
separate construction-level comparison with Szöllősi's Construction 3.1.
The separate algebraic-atlas geometry is also
outside the Lean formal boundary. Its retained exact and interval
calculations are reproducible from [`certificates/`](certificates/README.md).
See
[`LEAN_ASSUMES_AND_PROVES.md`](LEAN_ASSUMES_AND_PROVES.md) for the precise
statement of this boundary.

## Repository map

| Layer | Main files |
|---|---|
| Public paper-facing recombination | `PaperTheorem.lean` |
| Definitions, equivalence, and quotient | `Basic.lean`, `PhaseEquivalence.lean`, `HadamardQuotient.lean` |
| Finite-corner predicate and completion | `FiniteDilation.lean`, `Blocks.lean`, `BlockCompletion.lean` |
| Singular-corner and fibre analysis | `VanishingMinorReduction.lean`, `CandidateFibre.lean`, `InfiniteFibre*.lean`, `Dependent*.lean` |
| Block routing and Fourier closure | `BlockSwap*.lean`, `Classification.lean`, `Fourier*.lean`, `SimultaneousFourierNormalization.lean` |
| Tao branch | `TaoOrbit.lean`, `TaoAtlas.lean` |
| Intrinsic Karlsson normalization | `H2CanonicalForm.lean`, `H2BlockNormalization.lean`, `H2DegenerateNormalization.lean`, `H2KarlssonParametrization.lean`, `IntrinsicKarlssonSeam.lean` |
| Karlsson regular chart and seams | `Karlsson*.lean`, `H2ExceptionalSeam*.lean`, `H2RawPairSigns.lean`, `FourierSeamCertificate*.lean` |
| Post-classification geometry certificates | `certificates/` |

The files are collected under the `Hadamard6` namespace and directory.  The
root [`Hadamard6.lean`](Hadamard6.lean) imports
`Hadamard6.PaperTheorem`, which in turn fixes the complete public dependency
graph.

Two generated files are exact arithmetic backends rather than extra
classification layers: `KarlssonResidualCertificate.lean` is a generated
Bernstein-positivity table and `KarlssonWitnessResultants.lean` contains
generated resultant identities. Their short consumers are
`KarlssonResidualGlobal.lean` and `KarlssonMixedBlocks.lean`. The
affine-Fourier certificate is split across the
`FourierSeamCertificate*.lean` modules as a direct, theorem-structured
six-corner calculation rather than a generated table. This
separation matters when reading the project: start from `PaperTheorem.lean`
and descend into a certificate backend only when auditing that particular
arithmetic identity.

The cubic Fourier classification is organized the same way: the short
consumer is `FourierNormalizationClassification.lean`, while
`FourierCubicCases*.lean` and `FourierCubicTaoCases*.lean` contain the finite
exact case certificates. Their length records explicit arithmetic cases, not
additional hypotheses or alternative classification spines.

For a theorem-by-theorem correspondence with the manuscript, read
[`PAPER_PROOF_MAP.md`](PAPER_PROOF_MAP.md).

## Trust statement

The source audit rejects `sorry`, `admit`, project-defined `axiom` or
`constant`, source-level `opaque` or `unsafe` declarations, and unchecked
`native_decide`. It also rejects orphaned proof modules outside the
paper-facing dependency graph, preventing obsolete alternative APIs from
silently remaining in the project. `#print axioms` is run on all nine public
endpoints and may report only Lean/Mathlib's standard foundations `propext`,
`Classical.choice`, and `Quot.sound`.

The public theorem signatures contain no literature-facing theorem
parameters. The remaining axioms in the kernel report are precisely the
standard Lean/Mathlib foundations listed above.
