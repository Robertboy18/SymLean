import Lake

open Lake DSL

/-! A package that requires the consumer of `consumer/`, which requires SymLean, and tracks the
file that its module embeds: two levels of packages above SymLean. -/

package top

require consumer from ".." / "consumer"

lean_lib Top where
  globs := #[.submodules `Top]
  needs := #[`@/Top:SymLean.embeddedInputs]
