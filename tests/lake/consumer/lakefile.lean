import Lake

open Lake DSL

/-! A package that requires SymLean (the stand-in that `run.sh` puts next to it), forwards its
certificate profile, has a module setup facet and a library facet of its own and tracks the files
that its modules embed with `include_str`. -/

package consumer

require SymLean from ".." / "symlean" with
  NameMap.empty.insert `certificates ((get_config? certificates).getD "kernel")

/-- The consumer's own module setup, which SymLean must leave in place: it writes
`presetup-ran.txt` and then runs Lake's setup. -/
@[«module_facet»]
def consumerPresetup : ModuleFacetDecl :=
  .mk Module.presetupFacet <|
    mkFacetJobConfig (buildable := false) fun mod ↦ do
      if mod.pkg.baseName == `consumer then
        IO.FS.writeFile (mod.pkg.dir / "presetup-ran.txt") "ran"
      Module.presetupFacetConfig.run mod

/-- A library facet of the consumer's own, named like the last part of SymLean's, which neither
replaces SymLean's facet nor is replaced by it: it writes `consumer-facet-ran.txt` and tracks
nothing. -/
library_facet embeddedInputs (lib : LeanLib) : Array System.FilePath := do
  IO.FS.writeFile (lib.pkg.dir / "consumer-facet-ran.txt") "ran"
  return Job.pure #[]

lean_lib Plain where
  globs := #[.submodules `Plain]
  needs := #[`@/Plain:embeddedInputs]

lean_lib Probe where
  globs := #[.submodules `Probe]
  needs := #[`@/Probe:SymLean.embeddedInputs]

lean_lib Spellings where
  globs := #[.submodules `Spellings]
  needs := #[`@/Spellings:SymLean.embeddedInputs]

lean_lib Refused where
  globs := #[.submodules `Refused]
  needs := #[`@/Refused:SymLean.embeddedInputs]

/-- Macros, code that names the elaborator of `include_str`, and a declaration's own use of it,
in a library that does not list the facet. -/
lean_lib Macros where
  globs := #[.submodules `Macros]

/-- Modules that load those of `Macros`. -/
lean_lib Foreign where
  globs := #[.submodules `Foreign]
  needs := #[`@/Foreign:SymLean.embeddedInputs]

/-- A library with its root as its only glob: `Sparse.lean` does not import `Sparse.Hidden`, which
Lake still builds as part of `Sparse`, here for `SparseUser`. -/
lean_lib Sparse where
  needs := #[`@/Sparse:SymLean.embeddedInputs]

lean_lib SparseUser

/-- A large module, which `run.sh` writes, for the time that the search takes. -/
lean_lib Big where
  globs := #[.submodules `Big]
  needs := #[`@/Big:SymLean.embeddedInputs]
