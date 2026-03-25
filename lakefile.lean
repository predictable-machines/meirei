import Lake
open Lake DSL

package meirei where
  version := v!"0.1.0"

@[default_target]
lean_lib Meirei where
  roots := #[`Meirei]
