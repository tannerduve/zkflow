import Lake
open Lake DSL

package «zk_lean_compiler» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
     "https://github.com/leanprover-community/mathlib4.git" @ "37df177aaa770670452312393d4e84aaad56e7b6"

require ZKLeanEcosystem from git "https://github.com/GaloisInc/zk-lean.git" @ "21b5a46ea0b95472ce610f0588707be8969103d3"

require Parser from git "https://github.com/fgdorais/lean4-parser" @ "04dab179aa3d9a7150f105ddba70738098bd68d4"

@[default_target]
lean_lib «ZkLeanCompiler» where
  -- add any library configuration options here

lean_exe zkflow_demo where
  root := `ZkLeanCompiler.DemoMain
