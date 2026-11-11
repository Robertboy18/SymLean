# What a SymLean proof trusts

Every theorem of SymLean is checked by Lean's kernel. This file lists everything else a reader relies
on, each with the reason it is there. `bash scripts/audit.sh` lists the trusted constants below from
the built library.

## Always

- Lean 4.35.0's kernel and the axioms `propext`, `Classical.choice` and `Quot.sound`: every proof rests
  on them, and `scripts/audit.sh` reports any constant of the library that uses another axiom.
- Mathlib v4.35.0 (`56a00585`): the statements use its definitions (`Real.arctan`, the interval and
  Bochner integrals, `IntegrableOn`, `HasSum`, `tsum`), so they mean what those definitions mean.
- The SymLean definitions that appear in printed statements: `CAS.erf` (the definition of Mathlib
  pull request #34053), `CAS.Analysis.SpecialFunctions.legendre`, `CAS.AlgRoot.real` and
  `CAS.AlgRoot.complex` (`Classical.epsilon` choices, meaningful under `real_spec` and
  `complex_spec`), `coeffEval` and `polyC` (Mathlib's `Polynomial.ofCoeffList` mapped to `ℂ`), the
  relations `EnclosedOn`, `BoundOn`, `ApproxOn` and `ResidualBound` of
  `CAS/Certificate/Relations.lean`, `CAS.Exact.exprFn` with `CAS.Verified.Expr` and its evaluation,
  and the rational boxes: a reader must read them to know what an answer states.
- Embedded inputs: a theorem proved from `include_str` or `json_data%` is about the file's content
  when the module was built, and the `SymLean.embeddedInputs` facet makes Lake rebuild when the file
  changes, within the exclusions documented in `CAS/IncludeStr.lean`.
- Lake's rebuild rule: a module-system importer is not rebuilt when only the compiled code of an
  imported tactic changes, so a `#guard_msgs` that pins tactic output can replay a stale message until
  that module is rebuilt.

## Only in the fast profile

- `set_option cega.nativeCertificates true` or `lake build -R -Kcertificates=fast` lets `cega [fast]`
  check finite certificates with compiled code through `Lean.ofReduceBool`; this trusts Lean's
  compiler and runtime, and the theorem shows it in its axioms (`…._native.cegaFast.ax_*`,
  `tests/cega/Readme.lean`). Off by default.

## Compiled code that cannot reach a theorem

- 8 `implemented_by` attributes on 8 unsafe definitions: `CAS.Numerics.evalNatTerm`, `evalRowFun`,
  `evalString` and `natCompact` (evaluate terms while Lean elaborates, or keep large literals out of
  the generated C), and `CAS.Tactic.RouteRegistry.evalCloser`, `evalCommandBackend`,
  `evalFactorProvider` and `evalGoalPredicate` (run registered routes): a wrong result makes a tactic
  fail or skip a route; the kernel still checks any proof it produces.
- 6 `@[csimp]` lemmas, `fin_cases_eq_direct`, `fin_cons_eq_direct`, `vecCons_eq_vecConsLookup`,
  `translatedLogPanelInterval_eq_shared`, `factorRow_eq_factorRowFast` and `twoStageRow_eq_fast`,
  one per constant: kernel-proved equations that only compiled code uses, so they matter only in the
  fast profile and in `#eval`.
- 158 opaque and 481 partial constants, from `partial def`s and their compiled
  copies: the kernel never unfolds them, so no proof depends on their code; a statement that
  mentions one says nothing about its value.

## Searches, which are trusted for nothing

- The optional oracles of `CASOracle` (SymPy, SageMath, FLINT, Maxima, PARI/GP, Gappa, through our
  Lean 4.35 port of DSLean at `1b5f22ff`) and Hex's searches in the optional `CASHex`: they only
  propose answers, which become theorems through kernel-checked proofs.
- FloatLib 3.1.0 (`0fe4f04`): its executable floats run in compiled searches and `#eval`; its interval
  theorems are kernel-checked.

## Documentation

- The website compiles its ordinary cells; the Hex and oracle cells are quoted from files that only
  their own builds compile.
