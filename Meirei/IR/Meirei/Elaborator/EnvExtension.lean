/-
  Meirei Environment Extension

  Persistent storage for elaborated Meirei code. Stores the pretty-printed
  Lean syntax for each Meirei function so `#meirei_print` can display it,
  even for `partial def` functions where `#print` only shows opaque constants.
-/

import Lean

open Lean

namespace Meirei

abbrev MeireiCodeMap := Std.HashMap Name String

-- Stores (funcName, prettyPrintedLeanCode) pairs. Persists across modules
-- via olean serialization so #meirei_print works on imported definitions.
initialize meireiCodeExt : SimplePersistentEnvExtension (Name × String) MeireiCodeMap ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays => Id.run do
      let mut m : MeireiCodeMap := {}
      for entries in arrays do
        for (n, s) in entries do
          m := m.insert n s
      return m
    addEntryFn := fun m (n, s) => m.insert n s
  }

end Meirei
