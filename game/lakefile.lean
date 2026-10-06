import Lake
open Lake DSL

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

-- Use the GameServer from a `lean4game` folder lying next to the game on your
-- local computer. Activated with `lake update -Klean4game.local`.
-- Deactivate local version with `lake update -R`.
meta if get_config? lean4game.local |>.isSome then
require GameServer from "../lean4game/server"
else
require GameServer from git
  "https://github.com/leanprover-community/lean4game.git" @ leanVersion / "server"

package Game where
  leanOptions := #[
    ⟨`linter.all, false⟩,
    ⟨`pp.showLetValues, true⟩,
    ⟨`tactic.hygienic, false⟩]
  moreLeanArgs := #[
    "-Dtrace.debug=false"]
  moreServerOptions := #[
    ⟨`trace.debug, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ leanVersion

@[default_target]
lean_lib Game
