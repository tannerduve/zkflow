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

require ZKLeanEcosystem from git "https://github.com/GaloisInc/zk-lean.git" @ "main"

@[default_target]
lean_lib «ZkLeanCompiler» where
  -- add any library configuration options here

lean_lib «Frontend» where
  -- Optional: specify where the source files live
  srcDir := "ZkLeanCompiler/Frontend"

@[default_target]
lean_exe ZkLeanCompiler.Frontend.CompileZkProgram where
  root := `ZkLeanCompiler.Frontend.CompileZkProgram
