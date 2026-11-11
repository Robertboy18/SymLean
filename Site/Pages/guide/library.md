+++
id = "library"
kind = "guide"
title = "The library"
summary = "The public imports, how the modules are organized, the registries that extend the tactics, and how to check a change."
related_guides = ["tactics", "certificates", "hex", "oracles"]
tutorials = ["trust"]
+++

Most of the time you want `import CAS`, which brings in the calculator and the tactics. A file that needs less can import just the module that owns what it uses. If a file only proves derivatives with `cas`, say, it needs no more than

```
import CAS.ExactTactic
```

In library code my rule is stricter: always import the narrowest module that defines what you use.

## Public imports {#imports}

- `CAS.ExactTactic`: `cas` and `cas_nf`, with checked differentiation of `deriv`, `HasDerivAt` and `HasDerivWithinAt` statements and checked regularity of `DifferentiableAt`, `Differentiable` and `ContDiff` statements.
- `CAS.IntegrationTactic`: the integral route of `cas`, with primitive search, one integration-by-parts step and `cas [integrate primitive := F]`.
- `CAS.CEGA`: checked rational interval queries and the `cega` tactic.
- `CAS.Reporting`: the reporting tactics `cas?` and `cega?`.
- `CAS.Command.Simplification`, `CAS.Command.Solving`, `CAS.Command.Differential`, `CAS.Command.Integration` and `CAS.Command.CEGA`: the commands `#cas [simplify]`, `#cas [solve x]` and `#cas [reduce x]`, `#cas [derive]` and `#cas [grad]`, `#cas [integrate]`, and the box queries such as [[enclose]].
- `CAS.Numerics.Tactic`: `cega [batch := n]`, which `import CAS` leaves out.

The exact theorems, the numerical certificates and the polynomial algorithms have no umbrella module, and that’s deliberate. A file imports the modules of `ClosedForm`, `Exact`, `Continuum` or `Polynomial` that it uses, and nothing else.

`CAS.ExactTactic`, `CAS.IntegrationTactic` and `CAS.CEGA` import no differential operator beyond Mathlib’s. A package that defines its own Euclidean derivative operators registers a backend through `CAS.Tactic.DerivativeRegistry`, and importing the operator definitions alone doesn’t change what the tactics prove.

## How the library is organized {#layers}

The modules under `CAS` fall into layers, and the module documentation of each one states its contracts. These are the main layers:

- `Expr` and `Elaboration`: the checked expression language `Verified.Expr`, its real semantics, and the reflection of Lean terms into it.
- `ClosedForm` and `Exact`: exact normal forms, the side-conditioned rewrite passes, and the theorems that close exact goals.
- `Calculus` and `Integration`: symbolic derivatives with their analytic theorems, series, limits, linear ODEs, and the integration planner with its certificates.
- `Continuum`, `Certificate` and `CEGA`: interval evaluation over FloatLib, the certificate relations `EnclosedOn`, `BoundOn`, `ApproxOn` and `ResidualBound`, quadrature, and the `cega` frontend.
- `Numerics`: finite numerical certificates for large tables, JSON importers for exact data, and their kernel checks. Most of its modules, the packed rows, the binary64 words, the grid balls and the trigonometric tables among them, are kernels for certificate programs outside the library, and no command or tactic uses them.
- `Polynomial`: sparse polynomial arithmetic, gcds and division, and real-root certificates.
- `Tactic` and `Command`: the tactic frontends and the `#cas` commands.
- `Examples`: compiled examples. Every `#cas` command there runs under `#guard_msgs`, which checks the whole report or the parts the file records, so a change in the checked text fails the build.

Four smaller layers support them. `Analysis` holds the analytic facts behind some commands: splines, Hilbert transforms, quadratic forms and the positive-definiteness certificate, and bounds for Legendre polynomials, logarithms and trigonometric functions. `Domain` states side conditions on a patch, `PositiveOn` and `NonzeroOn`, together with the patch covers. `NumberTheory` has the congruence and modular-power theorems. `Route` pairs certificates with the planner steps that built them, and the steps there are diagnostic data, not evidence.

## Certificates and backends {#certificates}

Under the tactics, the lower-level interfaces expose `Verified.Expr` in typed certificate signatures. You use them to build reusable exact, residual, enclosure, approximation and quadrature certificates. The conclusions of these certificates are ordinary propositions, `Set.EqOn`, `ResidualBound`, `EnclosedOn`, `BoundOn` and `ApproxOn`, so a certificate’s conclusion can be used like any other theorem. The certificate structures live in focused modules under `CAS/Certificate`, again with no umbrella module. Ordinary Lean theorems restrict a certificate to a smaller domain or give it a weaker error budget, and [[cega-using|`cega using certificate`]] projects it.

The numerical engine is [FloatLib](https://github.com/lean-dojo/FloatLib). `RationalInterval` extends FloatLib’s rational intervals with the invariant `lo ≤ hi`, and the adapters of `CAS/Continuum/Interval` carry FloatLib’s containment theorems over to real enclosures. When sums need controlled denominators, `dyadicHull` rounds the endpoints outward onto a common grid, the lower endpoint down and the upper one up, the way (5.14) of [Rump 2010](https://doi.org/10.1017/S096249291000005X) rounds an interval to floating-point bounds. `RealIntervalBackend` then turns interval membership into real enclosures and error budgets. And for FloatLib’s own generic evaluator, `CAS.Expr.FloatLib` translates an expression with `Expr.toFloatLib`, and `eval_toFloatLib` preserves its real value when the coordinate tables agree and every real-power base is positive.

Large certificates come with data files, and data files bring a problem. A certificate program outside the library reads its tables with `include_str`, as the JSON importers of `Numerics` expect. But Lake rebuilds a module when its source changes, not when such a file does, so after you edit a table the build could keep a theorem about the old one. To prevent that, the program’s library lists the facet `SymLean.embeddedInputs` that SymLean’s `lakefile.lean` defines, as SymLean’s own libraries do:

```
lean_lib Certificates where
  needs := #[`@/Certificates:SymLean.embeddedInputs]
```

With the facet listed, editing a data file rebuilds the modules of the library, meaning all the modules that Lake builds as part of it: those of its globs, their local imports and every module under the directory of a root. The facet finds the files by searching the text of each module for `include_str` followed by a string literal, over several lines and comments if need be, and it decodes the literal as Lean does. A text search only works if the text is what Lean reads, and the check of `CAS.IncludeStr`, which `CAS.Numerics.Json` imports publicly, makes sure of that. It accepts an `include_str` only when its keyword and its path, one string literal with only whitespace and comments before it, are the text of the module’s file at that place, which is where the search looks. It refuses any other form with a message that says what to write instead, for instance a path `"a" ++ ".json"`, Lean’s own `"dir" / "file"`, an `include_str` that a macro or notation produces, or one that code parses from a string and elaborates.

The facet also guards the check itself. It stops the build at a module of the library that

- contains `include_str`, if only in a comment, but does not load `CAS.IncludeStr` through its public imports (through any import, in a file outside the module system), so that every module that can expand its macros and notations loads the check as well;
- loads a module of the workspace whose text can produce `include_str` in another module, because it has `include_str` in a string, in a syntax quotation or in a command other than a declaration, but does not load `CAS.IncludeStr`;
- has or loads code that names the syntax kind or an elaborator of `include_str` (`includeStr`, `elabIncludeStr`, `checkIncludeStr`), as code that adds, replaces or removes such an elaborator does. `CAS.IncludeStr` itself is the exception.

Put together, this means that in a library that lists the facet, every file that Lean reads through `include_str` while it elaborates a module of the library is tracked, or the build stops. Three things stay outside. An elaborator or meta code that reads the file itself, with `IO.FS.readFile` say. Code that builds `include_str` at run time from pieces of text, so that neither `include_str` nor `includeStr` is in its text, or elaborates it under a file name and a file map that it sets up itself. And macros from outside the workspace, which means Lean’s own modules, none of which produces `include_str`.

The facet’s name carries the package’s because Lake keeps one facet table for the whole workspace, and a facet replaces any earlier one of the same name.

## Extending the tactics {#extending}

You extend the tactics through explicit registries, and adding an entry to one adds no assumption:

- `@[cas_deriv]` registers a `HasDerivAt` theorem for the derivative route of `cas`. Its premises must be proved at each use, and `cas.maxDerivativeSteps` bounds the search. A definition of the current module with a registered rule stays folded, and the rule differentiates it.
- `@[cas_route name (priority := p) (goal := g)]` registers a route of `cas` and `cas?` that runs at priority `p` on goals that `g` accepts, and `CAS.ExactTactic.routeOrder` lists every route in the order `cas` tries them. `CAS.IntegrationTactic` registers the integral route, `CAS.CEGA` the box route, `CAS.Command.Ideal` the route for ideal equalities and memberships, the commands the route that proves their statements as goals, and `CASHex` its Hex routes. Importing the registry alone installs none of them.
- `cega_carrier` registers a type of attempts with its projection to a certificate, which plain `cega` then tries.
- `CAS.Tactic.DerivativeRegistry` takes a backend for Euclidean derivative operators.

My rule here is to extend a registry only when the semantic theorem behind the new entry already exists. A registry chooses which theorem to apply. It never replaces one.

## Checking a change {#checking}

These are the standards I hold the library to, and I’d ask the same of any change. Follow Mathlib’s conventions and the layout of the nearest file: a docstring on every public declaration, a module docstring in every file, lines within 100 characters, and no `sorry`, `admit`, new axiom or direct `native_decide`. Reuse Mathlib’s lemmas and FloatLib’s interval arithmetic instead of writing local copies, and leave to Hex what Hex does, so a new factoring or primality search belongs in `CASHex`, through Hex, and not in the core library. Real-root isolation is the one exception. The core keeps its own square-free parts and isolation so that `roots`, `reduce`, `solve` and `minimize` work without Hex. Two rules matter more than the rest: a route may close a goal only with a proof of the original goal, and a refusal must restore the proof state.

Credit matters to me, so cite each idea you borrow and each program you use under `## References` in the module docstring. A paper or a book gets its authors, title, venue, year and link. A program gets its authors or project, title and link, or the paper its project asks users to cite, along with the version tested or the release or revision pinned. The program itself gets a year only where the project’s citation page or release record gives one for that version.

To check a change, build the changed module first and then everything:

```
lake build +CAS.Calculus.Series
lake build
bash tests/cega/run.sh
bash tests/docs/run.sh
bash tests/lake/run.sh
```

`lake build` applies the repository’s options, warnings as errors among them, and compiles the examples. The three test scripts cover what the library build can’t. `tests/cega` holds the native certificate tests, which run outside the library build because they turn native checking on. `tests/docs` holds the test of the documented tactic forms, which reads docstrings that a module of the library cannot see. And `tests/lake` holds the tests of `lakefile.lean`: the certificate profiles, the tracking of the files that modules embed, the paths that the build refuses to track, the time that the scan of a large module takes, and a dependent package with a module setup facet and a library facet of its own. A change that touches `CASHex` or the modules it imports should also be built with the [[hex|Hex routes]], and one that touches `CASOracle` with the oracle tests of the [[oracle]] page.

This site is checked the same way, because an example nobody ran is one I wouldn’t trust. `bash Site/Tools/build.sh` compiles every cell of every page against the library, except the quoted ones, and the build fails when a cell that should run reports an error or a warning, when a cell that shows a failure doesn’t fail, when a cell’s output lacks the text its fence expects, when a quoted cell is not verbatim in the file it quotes, when a link or an anchor is broken, or when a form or a call of the command registry has no reference page.
