import Lake
open Lake DSL

package «lean_verus» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- require ManySortedModelTheory from git
--   "https://github.com/Mathias-Stout/Many-sorted-model-theory.git" @ "main"

require ManySortedModelTheory from git
  "https://github.com/SSSPigeon/AIR-Many-sorted-model-theory.git" @ "main"


@[default_target]
lean_lib «LeanVerus» where
  -- add any library configuration options here
