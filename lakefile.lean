import Lake
open Lake DSL

package «ai-tutor-lean-proofs» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «AiTutorLeanProofs» {
  -- add any library configuration options here
  -- adding lean copilot as a dependency
  moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
}

require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.1.1"